import os
import re
import csv

from tabulate import tabulate, SEPARATING_LINE

working_dir = "underapproximation_type/data/validation"
results_file_regex = r"prog[0-9]+\.ml.result.csv$"


""" def run_synthesis_aux(cmd):
    invoc_cmd(verbose, cmd, rescode_non_zero, None, cwd=None) """


def fix_name(name):
    if "sized" in name:
        return "Sized List"
    elif "even" in name:
        return "Even List"
    elif "sorted" in name:
        return "Sorted List"
    elif "bst" in name:
        return "BST"
    elif "duplicate" in name:
        return "Duplicate List"
    elif "unique" in name:
        return "Unique List"
    elif "depth" in name:
        return "Sized Tree"
    elif "complete" in name:
        return "Complete Tree"
    elif "rbtree" in name:
        return "Red-Black Tree"
    else:
        return name


if __name__ == "__main__":
    list_stats = []
    tree_stats = []
    stlc_stats = []
    for benchmark_dir in os.listdir(working_dir):
        if "combined_stlc_gen" in benchmark_dir:
            continue
        b_path = "{}/{}".format(working_dir, benchmark_dir)
        benchmark_stats = []
        if os.path.isdir(b_path):
            print("looking in {}".format(b_path))
            d = os.listdir(b_path)
            d.sort()

            d = list(
                filter(
                    lambda filename: re.search(
                        results_file_regex, filename, re.MULTILINE
                    ),
                    d,
                )
            )

            for idx, filename in enumerate(d, start=1):
                stats = {}
                n = filename.split(".")[0].removeprefix("prog")
                name = ""
                if n == "1":
                    name = "{} {}".format(fix_name(benchmark_dir), n)
                elif idx == len(d):
                    name = "sketch"
                else:
                    name = n
                print(name)
                stats["name"] = name
                with open("{}/{}".format(b_path, filename), "r") as f:
                    reader = csv.DictReader(f)
                    """  reader["fielname"] = filename """
                    for row in reader:
                        print(row[" Queries"])
                        stats["#Holes"] = row[" #Holes"]
                        stats["Repair Size"] = row[" Repair Size"]
                        stats["#Queries"] = row[" Queries"]
                        stats["#Terms"] = row[" #Terms"]
                        print(row[" Abd Time"])
                        stats["Abduction Time(s)"] = row[" Abd Time"]

                        print(row[" Synth Time"])
                        stats["Synthesis Time(s)"] = row[" Synth Time"]

                        print(row[" Total Time"])
                        stats["Total Time(s)"] = row[" Total Time"]
                benchmark_stats.append(stats)
            # print(benchmark_stats)
            """ print(
                tabulate(
                    benchmark_stats, headers="keys", tablefmt="latex", stralign="right"
                )
            ) """

        if benchmark_stats:
            """if evaluation_stats:
            evaluation_stats.append((SEPARATING_LINE,))"""
            if "list" in benchmark_dir:
                list_stats += benchmark_stats
            elif "tree" in benchmark_dir or "bst" in benchmark_dir:
                tree_stats += benchmark_stats
            else:
                stlc_stats += benchmark_stats

    # HACK: TODO: Fix this mess
    def helper(s: re.Match[str]) -> str:
        string = s.group(0)

        print("here")
        print(string)
        print((string[:-1:]))

        if "sketch" in string:
            return string
        elif "\\\\" in string:
            return "\\\\ \n\\midrule" + string[2:]
        else:
            return (string[:-1:]) + " \\midrule " + string[-1]

    for evaluation_stats in [list_stats, tree_stats, stlc_stats]:
        # print(evaluation_stats)
        latex_table = tabulate(
            evaluation_stats, headers="keys", tablefmt="latex", stralign="right"
        )

        latex_table = re.sub(r"\\\\\n\s+[a-zA-Z]+", helper, latex_table)
        print(latex_table)
