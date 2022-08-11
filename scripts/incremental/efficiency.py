from pydriller import Repository, Git
import utils
import psutil
import multiprocessing as mp
import os
import subprocess
import itertools
import shutil
import json
from datetime import datetime
import sys
import pandas as pd
from pathlib import Path

# benefitted_commits = ['3a2d33d5a37c69e0e0a58773954fca65fc9c3efb', '2c877fa149842087cf24e4494601c71adf2290d5', '9a4c22db0388b3a6a6e061b3bf6e35b542ba020a',
#                       'edda0c60b3df7910046d3d0f5325491319bd973f', 'e56154a68711422f6bb68e06bd5b35fa5bc6df31', '6199a89170273c507df58cec136040f8805ab799',
#                       'd92583ed330f4c1f5f29fc1fc7c01d2a19d12319', '3f85d1dcc1b4860ccaeedc502dfaa1b6ef8a9b76', 'a0a9560258cef3fa7dcd16e5f24eb087867641a0',
#                       '57957ab6cf7c74e593ff9644a22e921077fdc47a', '039b388c82b159479df6a6a02efe124b28fafbde', 'be14dbffef738935ce51e01d2ce20399c090399d',
#                       '8f6a1b5318795f20fc01503803f612fa2ac5878d', '8db9d59dacb1f2eeef0b0450bd391e5b55710095', '43dc0b329567904b65aefb54b0e63c97a905bbce',
#                       '99cc94529d3230b2c296959954031a1d396b49e9', '8f6a1b5318795f20fc01503803f612fa2ac5878d', '2f738d580544208189b0e31619bd915d34a92577']
#
# benefitted_commits = ['e56154a68711422f6bb68e06bd5b35fa5bc6df31']

# specific_commits = ["ae4670466c5db56493f356c1a81e8cbefef3271e"]

################################################################################
# Usage: python3 incremental_smallcommits.py <full_path_analyzer_dir> <number_of_cores>
# Executing the script will overwrite the directory 'result_efficiency' in the cwd.
# The script for building the compilation database is assumed to be found in the analyzers script directory and the
# config file is assumed to be found in the conf directory of the analyzers repository.
# The single test runs are mapped to processors according to the coremapping. The one specified in the section below
# should work for Intel machines, otherwise you might need to adapt it according to the description.
if len(sys.argv) != 3:
      print("Wrong number of parameters.\nUse script like this: python3 parallel_benchmarking.py <path to goblint directory> <number of processes>")
      exit()
result_dir    = os.path.join(os.getcwd(), 'result_efficiency')
maxCLOC       = 5000 # can be deactivated with None
url           = "https://github.com/facebook/zstd"
repo_name     = "zstd"
build_compdb  = "build_compdb_zstd.sh"
conf_base     = "min_incr_zstd" # very minimal: "zstd-minimal"
conf_incrpost = "zstd-race-incrpostsolver"
begin         = datetime(2018,1,1)
to            = datetime(2022,1,1) # minimal subset: datetime(2021,8,4)
diff_exclude  = ["build", "doc", "examples", "tests", "zlibWrapper", "contrib"]
analyzer_dir  = sys.argv[1]
only_collect_results = False # can be turned on to collect results, if data collection was aborted before the creation of result tables
################################################################################
try:
    numcores = int(sys.argv[2])
except ValueError:
    print("Parameter should be a number.\nUse script like this: python3 parallel_benchmarking.py <absolute path to goblint directory> <number of processes>")
    exit()
avail_phys_cores = psutil.cpu_count(logical=False)
allowedcores = avail_phys_cores - 1
if not only_collect_results and numcores > allowedcores:
    print("Not enough physical cores on this machine (exist: ", avail_phys_cores, " allowed: ", allowedcores, ")")
    exit()
# For equal load distribution, choose a processes to core mapping,
# use only physical cores and have an equal number of processes per cache.
# The layout of physical/logical cores and sharing of caches is machine dependent. To find out use: 'lscpu --all --extended'.
# For our test server:
coremapping1 = [i for i in range(numcores - numcores//2)]
coremapping2 = [i for i in range(avail_phys_cores//2, avail_phys_cores//2 + numcores//2)]
coremapping = [coremapping1[i//2] if i%2==0 else coremapping2[i//2] for i in range(len(coremapping1) + len(coremapping2))]
################################################################################

def filter_commits_false_pred(repo_path):
    def pred(c):
        relCLOC = utils.calculateRelCLOC(repo_path, c, diff_exclude)
        return relCLOC == 0 or (maxCLOC is not None and relCLOC > maxCLOC) or relCLOC < 500
    return pred

def analyze_small_commits_in_repo(cwd, outdir, from_c, to_c):
    count_analyzed = 0
    count_skipped = 0
    count_failed = 0
    analyzed_commits = {}
    repo_path = os.path.join(cwd, repo_name)

    for commit in itertools.islice(itertools.filterfalse(filter_commits_false_pred(repo_path), Repository(url, since=begin, to=to, only_no_merge=True, clone_repo_to=cwd).traverse_commits()), from_c, to_c):
        gr = Git(repo_path)

        #print("\n" + commit.hash)
        #print('changed LOC: ', commit.lines)
        #print('merge commit: ', commit.merge)

        # skip merge commits and commits that have no or less than maxCLOC of relevant code changes
        relCLOC = utils.calculateRelCLOC(repo_path, commit, diff_exclude) # use this to filter commits by actually relevant changes
        #print("relCLOC: ", relCLOC)
        if relCLOC == 0 or (maxCLOC is not None and relCLOC > maxCLOC):
            #print('Skip this commit: merge commit or too many relevant changed LOC')
            count_skipped+=1
            continue

        # analyze
        try_num = from_c + count_analyzed + count_failed + 1
        outtry = os.path.join(outdir, str(try_num))
        parent = gr.get_commit(commit.parents[0])
        #print('Analyze this commit incrementally. #', try_num)

        utils.reset_incremental_data(os.path.join(cwd, 'incremental_data'))
        failed = True
        try:
            #print('Starting from parent', str(parent.hash), ".")
            outparent = os.path.join(outtry, 'parent')
            os.makedirs(outparent)
            add_options = ['--disable', 'incremental.load', '--enable', 'incremental.save']
            utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, parent.hash, outparent, conf_base, add_options)

            # print('And again incremental, this time with incremental postsolver')
            outchildincrpost = os.path.join(outtry, 'everything-disabled')
            os.makedirs(outchildincrpost)
            add_options = ['--enable', 'incremental.load', '--disable', 'incremental.save', '--disable',
                           'incremental.detect-local-renames', '--disable', 'incremental.detect-global-renames']
            utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, commit.hash, outchildincrpost, conf_base,
                                 add_options)

            print("Done")

            #print('And now analyze', str(commit.hash), 'incrementally.')
            outchild = os.path.join(outtry, 'everything-enabled')
            os.makedirs(outchild)
            add_options = ['--enable', 'incremental.load', '--disable', 'incremental.save', '--enable', 'incremental.detect-local-renames', '--enable', 'incremental.detect-global-renames']
            utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, commit.hash, outchild, conf_base, add_options)


            outchild = os.path.join(outtry, 'local-enabled')
            os.makedirs(outchild)
            add_options = ['--enable', 'incremental.load', '--disable', 'incremental.save', '--enable', 'incremental.detect-local-renames', '--disable', 'incremental.detect-global-renames']
            utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, commit.hash, outchild, conf_base, add_options)

            outchild = os.path.join(outtry, 'everything-enabled-rec')
            os.makedirs(outchild)
            add_options = ['--enable', 'incremental.load', '--disable', 'incremental.save', '--enable',
                           'incremental.detect-local-renames', '--enable', 'incremental.detect-global-renames',
                           '--set', 'incremental.detect-global-renamed-func', 'recursive']
            utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, commit.hash, outchild, conf_base,
                                 add_options)

            #print('And again incremental, this time with incremental postsolver and reluctant')
            # outchildrel = os.path.join(outtry, 'child-rel')
            # os.makedirs(outchildrel)
            # add_options = ['--enable', 'incremental.load', '--disable', 'incremental.save', '--enable', 'incremental.reluctant.enabled']
            # utils.analyze_commit(analyzer_dir, gr, repo_path, build_compdb, commit.hash, outchildrel, conf_incrpost, add_options)

            count_analyzed+=1
            failed = False
        except subprocess.CalledProcessError as e:
            print('Aborted because command ', e.cmd, 'failed.')
            count_failed+=1
        os.makedirs(outtry, exist_ok=True)
        with open(os.path.join(outtry,'commit_properties.log'), "w+") as file:
            json.dump({"hash": commit.hash, "parent_hash": parent.hash, "CLOC": commit.lines, "relCLOC": relCLOC, "failed": failed}, file)
        analyzed_commits[try_num]=(str(commit.hash)[:6], relCLOC)

    num_commits = count_analyzed + count_skipped + count_failed
    print("\nCommits traversed in total: ", num_commits)
    print("Analyzed: ", count_analyzed)
    print("Failed: ", count_failed)
    print("Skipped: ", count_skipped)

def collect_data(outdir):
    data = {"Commit": [],
            "Failed?": [],
            "Changed LOC": [],
            "Relevant changed LOC": [],
            "Everything enabled - Changed functions": [],
            "Everything enabled - Added functions": [],
            "Everything enabled - Removed functions": [],
            "Everything enabled rec - Changed functions": [],
            "Everything enabled rec - Added functions": [],
            "Everything enabled rec - Removed functions": [],
            "Locals enabled - Changed functions": [],
            "Locals enabled - Added functions": [],
            "Locals enabled - Removed functions": [],
            "Everything disabled - Changed functions": [],
            "Everything disabled - Added functions": [],
            "Everything disabled - Removed functions": [],
            utils.header_runtime_parent: [],
            utils.header_runtime_everything_disabled: [],
            utils.header_runtime_locals_enabled: [],
            utils.header_runtime_everything_enabled: [],
            utils.header_runtime_everything_enabled_rec: [],
            utils.header_comp_runtime_everything_disabled: [],
            utils.header_comp_runtime_locals_enabled: [],
            utils.header_comp_runtime_everything_enabled: [],
            utils.header_comp_runtime_everything_enabled_rec: [],
            utils.header_anal_runtime_everything_disabled: [],
            utils.header_anal_runtime_locals_enabled: [],
            utils.header_anal_runtime_everything_enabled: [],
            utils.header_anal_runtime_everything_enabled_rec: []
            }
    for t in os.listdir(outdir):
        parentlog = os.path.join(outdir, t, 'parent', utils.analyzerlog)
        everything_enabled = os.path.join(outdir, t, 'everything-enabled', utils.analyzerlog)
        everything_enabled_rec = os.path.join(outdir, t, 'everything-enabled-rec', utils.analyzerlog)
        local_enabled = os.path.join(outdir, t, 'local-enabled', utils.analyzerlog)
        everything_disabled = os.path.join(outdir, t, 'everything-disabled', utils.analyzerlog)
        commit_prop_log = os.path.join(outdir, t, 'commit_properties.log')
        commit_prop = json.load(open(commit_prop_log, "r"))
        data["Changed LOC"].append(commit_prop["CLOC"])
        data["Relevant changed LOC"].append(commit_prop["relCLOC"])
        data["Failed?"].append(commit_prop["failed"])
        data["Commit"].append(commit_prop["hash"][:7])
        if commit_prop["failed"] == True:
            data[utils.header_runtime_parent].append(0)
            data[utils.header_runtime_everything_disabled].append(0)
            data[utils.header_runtime_locals_enabled].append(0)
            data[utils.header_runtime_everything_enabled].append(0)
            data[utils.header_runtime_everything_enabled_rec].append(0)
            data[utils.header_comp_runtime_everything_disabled].append(0)
            data[utils.header_comp_runtime_locals_enabled].append(0)
            data[utils.header_comp_runtime_everything_enabled].append(0)
            data[utils.header_comp_runtime_everything_enabled_rec].append(0)
            data[utils.header_anal_runtime_everything_disabled].append(0)
            data[utils.header_anal_runtime_locals_enabled].append(0)
            data[utils.header_anal_runtime_everything_enabled].append(0)
            data[utils.header_anal_runtime_everything_enabled_rec].append(0)
            data["Everything enabled - Changed functions"].append(0)
            data["Everything enabled - Added functions"].append(0)
            data["Everything enabled - Removed functions"].append(0)
            data["Everything enabled rec - Changed functions"].append(0)
            data["Everything enabled rec - Added functions"].append(0)
            data["Everything enabled rec - Removed functions"].append(0)
            data["Locals enabled - Changed functions"].append(0)
            data["Locals enabled - Added functions"].append(0)
            data["Locals enabled - Removed functions"].append(0)
            data["Everything disabled - Changed functions"].append(0)
            data["Everything disabled - Added functions"].append(0)
            data["Everything disabled - Removed functions"].append(0)

            continue
        parent_info = utils.extract_from_analyzer_log(parentlog)
        everything_enabled_info = utils.extract_from_analyzer_log(everything_enabled)
        everything_enabled_rec_info = utils.extract_from_analyzer_log(everything_enabled_rec)
        local_enabled_info = utils.extract_from_analyzer_log(local_enabled)
        everything_disabled_info = utils.extract_from_analyzer_log(everything_disabled)
        data["Everything enabled - Changed functions"].append(int(everything_enabled_info["changed"]))
        data["Everything enabled - Added functions"].append(int(everything_enabled_info["added"]))
        data["Everything enabled - Removed functions"].append(int(everything_enabled_info["removed"]))
        data["Everything enabled rec - Changed functions"].append(int(everything_enabled_rec_info["changed"]))
        data["Everything enabled rec - Added functions"].append(int(everything_enabled_rec_info["added"]))
        data["Everything enabled rec - Removed functions"].append(int(everything_enabled_rec_info["removed"]))
        data["Locals enabled - Changed functions"].append(int(local_enabled_info["changed"]))
        data["Locals enabled - Added functions"].append(int(local_enabled_info["added"]))
        data["Locals enabled - Removed functions"].append(int(local_enabled_info["removed"]))
        data["Everything disabled - Changed functions"].append(int(everything_disabled_info["changed"]))
        data["Everything disabled - Added functions"].append(int(everything_disabled_info["added"]))
        data["Everything disabled - Removed functions"].append(int(everything_disabled_info["removed"]))
        data[utils.header_runtime_parent].append(float(parent_info["runtime"]))
        data[utils.header_runtime_everything_enabled].append(float(everything_enabled_info["runtime"]))
        data[utils.header_runtime_locals_enabled].append(float(local_enabled_info["runtime"]))
        data[utils.header_runtime_everything_disabled].append(float(everything_disabled_info["runtime"]))
        data[utils.header_runtime_everything_enabled_rec].append(float(everything_enabled_rec_info["runtime"]))

        data[utils.header_comp_runtime_everything_enabled].append(float(everything_enabled_info["comp_runtime"]))
        data[utils.header_comp_runtime_locals_enabled].append(float(local_enabled_info["comp_runtime"]))
        data[utils.header_comp_runtime_everything_disabled].append(float(everything_disabled_info["comp_runtime"]))
        data[utils.header_comp_runtime_everything_enabled_rec].append(float(everything_enabled_rec_info["comp_runtime"]))

        data[utils.header_anal_runtime_everything_enabled].append(float(everything_enabled_info["anal_runtime"]))
        data[utils.header_anal_runtime_locals_enabled].append(float(local_enabled_info["anal_runtime"]))
        data[utils.header_anal_runtime_everything_disabled].append(float(everything_disabled_info["anal_runtime"]))
        data[utils.header_anal_runtime_everything_enabled_rec].append(float(everything_enabled_rec_info["anal_runtime"]))

    return data

def runperprocess(core, from_c, to_c):
    if not only_collect_results:
        psutil.Process().cpu_affinity([core])
    cwd  = os.getcwd()
    outdir = os.path.join(cwd, 'out')
    if not only_collect_results:
        if os.path.exists(outdir) and os.path.isdir(outdir):
          shutil.rmtree(outdir)
        analyze_small_commits_in_repo(cwd, outdir, from_c, to_c)
    data_set = collect_data(outdir)
    df = pd.DataFrame(data_set)
    #df.sort_index(inplace=True, key=lambda idx: idx.map(lambda x: int(x.split(":")[0])))
    print(df)
    df.to_csv('results.csv', sep =';')

def analyze_chunks_of_commits_in_parallel():
    processes = []

    # calculate actual number of interesting commits up-front to allow for similar load distribution
    iter = itertools.filterfalse(filter_commits_false_pred(os.path.join(os.getcwd(), repo_name)), Repository(url, since=begin, to=to, only_no_merge=True, clone_repo_to=os.getcwd()).traverse_commits())
    num_commits = sum(1 for _ in iter)
    print("Number of potentially interesting commits:", num_commits)
    perprocess = num_commits // numcores if num_commits % numcores == 0 else num_commits // numcores + 1
    print("Per process: " + str(perprocess))

    for i in range(numcores):
        dir = "process" + str(i)
        if not only_collect_results:
            os.mkdir(dir)
        os.chdir(dir)
        # run script
        start = perprocess * i
        end = perprocess * (i + 1) if i < numcores - 1 else num_commits
        if not only_collect_results:
            p = mp.Process(target=runperprocess, args=[coremapping[i], start, end])
            p.start()
            processes.append(p)
            # time.sleep(random.randint(5,60)) # add random delay between process creation to try to reduce interference
        else:
            runperprocess(coremapping[i], start, end)
        os.chdir(result_dir)

    for p in processes:
        p.join()

def merge_results():
    filename = "results.csv"
    frames = []
    for process_dir in os.listdir("."):
        path = os.path.join(process_dir, filename)
        if os.path.exists(path):
            t = pd.read_csv(path, index_col=0, sep=";")
            frames.append(t)
    if len(frames) > 0:
        df = pd.concat(frames)
        #df.sort_index(inplace=True, key=lambda idx: idx.map(lambda x: int(x.split(":")[0])))
        df.to_csv('total_results.csv', sep=";")


if not only_collect_results:
    os.mkdir(result_dir)
os.chdir(result_dir)

analyze_chunks_of_commits_in_parallel()
merge_results()
