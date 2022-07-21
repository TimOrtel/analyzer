from pathlib import Path
import csv

ed_runtime = "Runtime for commit (incremental + everything disabled)"
le_runtime = "Runtime for commit (incremental + locals enabled)"
ee_runtime = "Runtime for commit (incremental + everything enabled)"

ee_cf = "Everything enabled - Changed functions"
ee_af = "Everything enabled - Added functions"
ee_rf = "Everything enabled - Removed functions"
le_cf = "Locals enabled - Changed functions"
le_af = "Locals enabled - Added functions"
le_rf = "Locals enabled - Removed functions"
ed_cf = "Everything disabled - Changed functions"
ed_af = "Everything disabled - Added functions"
ed_rf = "Everything disabled - Removed functions"

def main():
    results_file = Path("result_efficiency/total_results.csv")
    with open(results_file) as rf:
        reader = csv.DictReader(rf, delimiter=';')
        # calc_locals_unchanged_funs(reader)
        calc_runtime(reader)


# calc in how many commits the local rename detection detected less changed functions as the everything disabled
def calc_locals_unchanged_funs(reader):
    benefited_rows = 0

    for row in reader:
        changed_ed = int(row[ed_cf])
        changed_le = int(row[le_cf])

        if changed_le < changed_ed:
            benefited_rows += 1
            print(row["Commit"])

    print(f"Total rows benefited: {benefited_rows}")


def calc_runtime(reader):
    le_faster_than_ed = 0
    ee_faster_than_ed = 0
    ee_faster_than_le = 0
    commit_count = 0
    total_ed_runtime = 0
    total_le_runtime = 0
    total_ee_runtime = 0

    for row in reader:
        if row["Failed?"] == "True":
            continue

        runtime_ed = float(row[ed_runtime])
        runtime_le = float(row[le_runtime])
        runtime_ee = float(row[ee_runtime])

        total_ed_runtime += runtime_ed
        total_le_runtime += runtime_le
        total_ee_runtime += runtime_ee

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

    def calc_performance_increase(first, second):
        abs_performance_increase = first - second
        relative_performance_increase = 1 - (second / first)
        return abs_performance_increase, relative_performance_increase

    abs_pe_le_to_ed, rel_pe_le_to_ed = calc_performance_increase(average_runtime_ed, average_runtime_le)
    abs_pe_ee_to_ed, rel_pe_ee_to_ed = calc_performance_increase(average_runtime_ed, average_runtime_ee)
    abs_pe_ee_to_le, rel_pe_ee_to_le = calc_performance_increase(average_runtime_le, average_runtime_ee)

    def print_performance_increase(abs: float, rel: float, basis: str, comparison: str):
        abs_formatted = "{:.2f}".format(abs)
        percent = "{:.2f}".format(rel * 100)
        print(f"Perfomance increase with basis {basis} and comparison {comparison}: Absolute={abs_formatted}; Relative={percent}%")

    print_performance_increase(abs_pe_le_to_ed, rel_pe_le_to_ed, "Everything disabled", "Local enabled")
    print_performance_increase(abs_pe_ee_to_ed, rel_pe_ee_to_ed, "Everything disabled", "Everything enabled")
    print_performance_increase(abs_pe_ee_to_le, rel_pe_ee_to_le, "Local enabled", "Everything enabled")

if __name__ == '__main__':
    main()
