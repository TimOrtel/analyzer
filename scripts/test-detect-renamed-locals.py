#!/usr/bin/python

import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from os.path import isdir
from pathlib import Path
from pycparser import c_ast, c_parser, parse_file
from pycparser.c_ast import TypeDecl, ArrayDecl, PtrDecl
from pycparser.c_generator import CGenerator

parser_errors = 0
struct_occurrences = 0
skips = 0
includes = 0
includes_only_assert = 0
invalid_solver = 0


def main():
    regression_folder = Path("./tests/regression")

    # execute_validation_test(regression_folder/"44-trier_analyzer", regression_folder/"44-trier_analyzer/21-Pproc.c")
    #
    # return

    excluded = [
        "44-trier_analyzer/33-recA.c",
        # Even though the same file is read in, the type of rec#i differes from int * to int?!
        "09-regions/25-usb_bus_list_nr.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "09-regions/07-kernel_list_rc.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "09-regions/08-kernel_list_nr.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "09-regions/15-kernel_foreach_nr.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "09-regions/14-kernel_foreach_rc.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/48-assign_spawn.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/40-rw_lock_rc.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/33-kernel_rc.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/39-rw_lock_nr.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/34-kernel_nr.c",  # linux/list.h: Datei oder Verzeichnis nicht gefunden
        "04-mutex/53-kernel-spinlock.c",  # Kernel is broken.
        "42-annotated-precision/25-34_01-nested.c",  # Wrong solver? slr3
        "42-annotated-precision/26-34_02-hybrid.c",  # slr4
        "56-witness/01-base-lor-enums.c",  # 0evals?
        "56-witness/02-base-lor-addr.c",  # 0evals?
        "56-witness/03-int-log-short.c",  # 0evals?
        "56-witness/04-base-priv-sync-prune.c",  # 0evals?
        "07-uninit/19-struct_in_union_bad.c", #Type uninion problems
        "44-trier_analyzer/09-G1.c", #Also renamed glob var
        "44-trier_analyzer/21-Pproc.c" #renamed function.
    ]

    # folder = regression_folder / "07-uninit"
    # for testFile in folder.iterdir():
    #     filename, extension = os.path.splitext(testFile.name)
    #     identifier = f"{folder.name}/{testFile.name}"
    #
    #     if extension == ".c" and not (identifier in excluded):
    #         execute_validation_test(folder, testFile)

    total_tests = 0
    executed_tests = 0

    for folder in regression_folder.iterdir():
        if isdir(folder):
            for testFile in folder.iterdir():
                filename, extension = os.path.splitext(testFile.name)
                if extension == ".c" and not (f"{folder.name}/{testFile.name}" in excluded):
                    total_tests += 1
                    if execute_validation_test(folder, testFile):
                        executed_tests += 1

    print(f"Executed {executed_tests}/{total_tests}")

    global parser_errors
    global struct_occurrences
    global skips
    global includes
    global invalid_solver
    global includes_only_assert

    print("Skipped due tue:")
    print("Parser errors: " + str(parser_errors))
    print("Struct occurrences: " + str(struct_occurrences))
    print("Skips (//Skip): " + str(skips))
    print(f"Includes: {includes}, of those only assert: {includes_only_assert}")
    print("Invalid solver: " + str(invalid_solver))


def execute_validation_test(folder: Path, test_file: Path):
    print(f"Executing test: {folder.name}/{test_file.name}")

    global parser_errors
    global struct_occurrences
    global skips
    global includes
    global invalid_solver
    global includes_only_assert

    extra_params = ""

    with open(test_file, "r") as filehandle:
        lines = filehandle.readlines()
        if lines[0].startswith("// PARAM:"):
            extra_params = lines[0][len("// PARAM:"):-1]
        if lines[0].startswith("// SKIP"):
            print("Skipped test.")
            skips += 1
            return False
        if any(x.startswith("#include") for x in lines):
            print("Skipped test because of include")
            includes += 1

            include_lines = [x for x in lines if x.startswith("#include")]

            if all("assert.h" in x for x in include_lines):
                includes_only_assert += 1

            return False
        if any("struct" in x for x in lines):
            print("Skipped because struct")
            struct_occurrences += 1
            return False

    if "slr3" in extra_params or "slr4" in extra_params:
        print("Aborted test due to invalid solver.")
        invalid_solver += 1
        return False

    updated_file = create_file_with_renamed_locals(test_file)

    if updated_file is None:
        print("Aborted test due to parsing error.")
        parser_errors += 1
        return False

    base = "./"

    args = f"--enable dbg.debug --enable printstats -v {extra_params}"

    subprocess.run(f"./goblint {args} --enable incremental.save {test_file}", shell=True, capture_output=True)

    command = subprocess.run(
        f"./goblint {args} --enable incremental.load --set save_run {base}/{test_file}-incrementalrun {updated_file.name}",
        shell=True, text=True, capture_output=True)

    found_line = False

    for line in command.stdout.splitlines():
        if line.startswith("change_info = "):
            match = re.search("; changed = (\d+)", line)
            change_count = int(match.group(1))
            if change_count != 0:
                print("-----------------------------------------------------------------")
                print(command.stdout)
                print("-----------------------------------------------------------------")
                print(f"Invalid change count={change_count}. Expected 0.")
                cleanup(folder, test_file, updated_file)
                sys.exit(-1)
            found_line = True
            break

    if not found_line:
        print("Could not find line with change count.")
        print(command.stdout)
        cleanup(folder, test_file, updated_file)
        sys.exit(-1)

    cleanup(folder, test_file, updated_file)

    return True


def cleanup(folder: Path, test: Path, updated_file):
    updated_file.close()
    shutil.rmtree(folder / f"{test.name}-incrementalrun")


class VarDeclVisitor(c_ast.NodeVisitor):

    def __init__(self):
        self.local_variables = []
        self.function_params = []

    def visit_FuncDef(self, node):
        if node.body.block_items is not None:
            for child in node.body.block_items:
                if isinstance(child, c_ast.Decl):
                    if isinstance(child.type, c_ast.TypeDecl) or isinstance(child.type, c_ast.ArrayDecl):
                        self.local_variables.append(child.name)
        if isinstance(node.decl, c_ast.Decl) and isinstance(node.decl.type, c_ast.FuncDecl):
            func_decl = node.decl.type
            if isinstance(func_decl.args, c_ast.ParamList):
                for arg in func_decl.args.params:
                    if isinstance(arg, c_ast.Decl):
                        self.function_params.append(arg.name)


class RenameVariableVisitor(c_ast.NodeVisitor):

    def __init__(self, rename_mapping):
        self.map = rename_mapping


    def visit_ID(self, node):
        if node.name in self.map:
            node.name = self.map[node.name]


    def visit_Decl(self, node):
        if isinstance(node.type, TypeDecl) or isinstance(node.type, ArrayDecl) or isinstance(node.type, PtrDecl):
            if node.name in self.map:
                new_name = self.map[node.name]
                node.name = new_name
                if isinstance(node.type, TypeDecl):
                    node.type.declname = new_name
                if isinstance(node.type, ArrayDecl):
                    node.type.type.declname = new_name
                if isinstance(node.type, PtrDecl):
                    node.type.type.declname = new_name

        if node.init is not None:
            self.visit(node.init)

        self.visit(node.type)


def create_file_with_renamed_locals(source_file: Path):
    try:
        ast = parse_file(source_file, use_cpp=True)
        v = VarDeclVisitor()
        v.visit(ast)

        rename_mapping = {}
        for local_var in (v.local_variables + v.function_params):
            rename_mapping[local_var] = local_var + "_updated"

        v = RenameVariableVisitor(rename_mapping)
        v.visit(ast)

        # print(ast)

        # print(CGenerator().visit(ast))

        tmp = tempfile.NamedTemporaryFile()
        with open(tmp.name, "w") as f:
            f.write(CGenerator().visit(ast))

        return tmp
    except:
        return None


if __name__ == '__main__':
    # create_file_with_renamed_locals("scripts/test.c")
    main()
