from pathlib import Path
import csv

ed_runtime = "Runtime for commit (incremental + everything disabled)"
le_runtime = "Runtime for commit (incremental + locals enabled)"
ee_runtime = "Runtime for commit (incremental + everything enabled)"
ee_rec_runtime = "Runtime for commit (incremental + everything enabled recursive)"

ee_cf = "Everything enabled - Changed functions"
ee_af = "Everything enabled - Added functions"
ee_rf = "Everything enabled - Removed functions"
ee_rec_cf = "Everything enabled rec - Changed functions"
ee_rec_af = "Everything enabled rec - Added functions"
ee_rec_rf = "Everything enabled rec - Removed functions"
le_cf = "Locals enabled - Changed functions"
le_af = "Locals enabled - Added functions"
le_rf = "Locals enabled - Removed functions"
ed_cf = "Everything disabled - Changed functions"
ed_af = "Everything disabled - Added functions"
ed_rf = "Everything disabled - Removed functions"

def main():
    #results_file = Path("/home/tim/Code/analyzer_results/700/result_efficiency/total_results.csv")
    #results_file = Path("/home/tim/Code/analyzer_results/500/total_results.csv")
    results_file = Path("/home/tim/Code/analyzer_results/combination.csv")
    with open(results_file) as rf:
        reader = csv.DictReader(rf, delimiter=';')
        calc_runtime(reader)
        # calc_runtime(reader)

def calc_considered(reader):
    total = 0
    failed = 0
    for row in reader:
        total += 1
        if row["Failed?"] == "True":
            failed += 1

    successful = total - failed

    print(f"total {total}; failed {failed}; successful {successful}")


# calc in how many commits the local rename detection detected less changed functions as the everything disabled
def calc_locals_unchanged_funs(reader):
    benefited_rows_le = []
    benefited_rows_ee = []
    benefited_rows_ee_rec = []

    count = 0

    for row in reader:
        count += 1
        changed_ed = int(row[ed_cf])
        changed_le = int(row[le_cf])
        changed_ee = int(row[ee_cf])
        changed_ee_rec = int(row[ee_rec_cf])

        commit_ = row["Commit"]
        if changed_le < changed_ed:
            benefited_rows_le += [commit_]

        if changed_ee < changed_ed:
            benefited_rows_ee += [commit_]

        if changed_ee_rec < changed_ed:
            benefited_rows_ee_rec += [commit_]

        if changed_ee > changed_ed:
            print(f"Worse: {commit_}: {changed_ee}-{changed_ed}")

    print(f"Total rows benefited from local changes: {len(benefited_rows_le)}; {benefited_rows_le}")
    print(f"Total rows benefited from everything enabled: {len(benefited_rows_ee)}; {benefited_rows_ee}")
    print(f"Total rows benefited from everything enabled rec: {len(benefited_rows_ee_rec)}; {benefited_rows_ee_rec}")
    print(str(count))


def calc_runtime(reader):
    le_faster_than_ed = 0
    ee_faster_than_ed = 0
    ee_faster_than_le = 0
    commit_count = 0
    total_ed_runtime = 0
    total_le_runtime = 0
    total_ee_runtime = 0
    total_ee_rec_runtime = 0

    for row in reader:
        if row["Failed?"] == "True":
            continue

        runtime_ed = float(row[ed_runtime])
        runtime_le = float(row[le_runtime])
        runtime_ee = float(row[ee_runtime])
        runtime_ee_rec = float(row[ee_rec_runtime])

        total_ed_runtime += runtime_ed
        total_le_runtime += runtime_le
        total_ee_runtime += runtime_ee
        total_ee_rec_runtime += runtime_ee_rec

        commit_count += 1

        if runtime_ee < runtime_ed:
            ee_faster_than_ed += 1

        if runtime_le < runtime_ed:
            le_faster_than_ed += 1

        if runtime_ee < runtime_le:
            ee_faster_than_le += 1

    average_runtime_ed = total_ed_runtime / commit_count
    average_runtime_le = total_le_runtime / commit_count
    average_runtime_ee = total_ee_runtime / commit_count
    average_runtime_ee_rec = total_ee_rec_runtime / commit_count

    def calc_performance_increase(first, second):
        abs_performance_increase = first - second
        relative_performance_increase = 1 - (second / first)
        return abs_performance_increase, relative_performance_increase

    abs_pe_le_to_ed, rel_pe_le_to_ed = calc_performance_increase(average_runtime_ed, average_runtime_le)
    abs_pe_ee_to_ed, rel_pe_ee_to_ed = calc_performance_increase(average_runtime_ed, average_runtime_ee)
    abs_pe_ee_rec_to_ed, rel_pe_ee_rec_to_ed = calc_performance_increase(average_runtime_ed, average_runtime_ee_rec)
    abs_pe_ee_to_le, rel_pe_ee_to_le = calc_performance_increase(average_runtime_le, average_runtime_ee)

    def print_performance_increase(abs: float, rel: float, basis: str, comparison: str):
        abs_formatted = '%.3g' % abs
        percent = '%.3g' % (rel * 100)
        print(f"Perfomance increase with basis {basis} and comparison {comparison}: Absolute={abs_formatted}; Relative={percent}%")

    print_performance_increase(abs_pe_le_to_ed, rel_pe_le_to_ed, "Everything disabled", "Local enabled")
    print_performance_increase(abs_pe_ee_to_ed, rel_pe_ee_to_ed, "Everything disabled", "Everything enabled")
    print_performance_increase(abs_pe_ee_rec_to_ed, rel_pe_ee_rec_to_ed, "Everything disabled", "Everything enabled rec")
    print_performance_increase(abs_pe_ee_to_le, rel_pe_ee_to_le, "Local enabled", "Everything enabled")

if __name__ == '__main__':
    main()
