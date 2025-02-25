import os
import re
import csv

from tabulate import tabulate, SEPARATING_LINE

working_dir = "underapproximation_type/data/validation"
results_file_regex = r"prog[0-9]+\.ml.result.csv$"


""" def run_synthesis_aux(cmd):
    invoc_cmd(verbose, cmd, rescode_non_zero, None, cwd=None) """

if __name__ == "__main__":
    evaluation_stats = []
    for benchmark_dir in os.listdir(working_dir):
        if "stlc" in benchmark_dir:
            continue

        b_path = "{}/{}".format(working_dir, benchmark_dir)
        benchmark_stats = []
        if os.path.isdir(b_path):
            print("looking in {}".format(b_path))
            d = os.listdir(b_path)
            d.sort()

            for filename in d:
                matches = re.search(results_file_regex, filename, re.MULTILINE)
                if matches:
                    stats = {}
                    n = filename.split(".")[0].removeprefix("prog")
                    name = ""
                    if n == "1":
                        name = "{} {}".format(benchmark_dir, n)
                    else:
                        name = n
                    print(name)
                    stats["name"] = name
                    with open("{}/{}".format(b_path, filename), "r") as f:
                        reader = csv.DictReader(f)
                        """  reader["fielname"] = filename """
                        for row in reader:
                            print(row[" Queries"])
                            stats["#Queries"] = row[" Queries"]
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
            evaluation_stats += benchmark_stats

    # print(evaluation_stats)
    latex_table = tabulate(
        evaluation_stats, headers="keys", tablefmt="latex", stralign="right"
    )

    def helper(s: re.Match[str]) -> str:
        string = s.group(0)

        print((string[:-1:]))

        return (string[:-1:]) + " \\midrule " + string[-1]

    latex_table = re.sub(r"\\\\\n\s+[a-zA-Z]", helper, latex_table)
    print(latex_table)
