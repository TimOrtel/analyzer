#!/usr/bin/python

import os
import re
import subprocess
import sys
from os.path import isdir
from pathlib import Path


def main():
    regression_folder = Path("../tests/regression")

    for folder in regression_folder.iterdir():
        if isdir(folder):
            for testFile in folder.iterdir():
                execute_validation_test(folder, testFile)


def execute_validation_test(folder: Path, test_file: Path):
    print(f"Executing test: {folder.name}/{test_file.name}")

    base = "./"

    args = "--enable dbg.debug --enable printstats -v"

    subprocess.run(f"../goblint {args} --enable incremental.save {test_file}", shell=True, capture_output=True)

    command = subprocess.run(
        f"../goblint {args} --enable incremental.load --set save_run {base}/{test_file}-incrementalrun {test_file}",
        shell=True, text=True, capture_output=True)

    found_line = False

    print(command.stdout)
    print(command.stderr)

    for line in command.stdout.splitlines():
        if line.startswith("change_info = "):
            match = re.search("; changed = (\d+)", line)
            change_count = int(match.group(1))
            if change_count != 0:
                print(f"Invalid change count={change_count}. Expected 0.")
                sys.exit(-1)
            found_line = True
            break

    if not found_line:
        print("Could not find line with change count.")
        sys.exit(-1)

    sys.exit(0)

if __name__ == '__main__':
    main()
