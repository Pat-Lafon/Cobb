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
        return "Sized List$^*$"
    elif "even" in name:
        return "Even List$^*$"
    elif "sorted" in name:
        return "Sorted List$^*$"
    elif "bst" in name:
        return "BST$^\\star$"
    elif "duplicate" in name:
        return "Duplicate List$^*$"
    elif "unique" in name:
        return "Unique List$^\\Diamond$"
    elif "depth" in name:
        return "Sized Tree$^*$"
    elif "complete" in name:
        return "Complete Tree$^\\star$"
    elif "rbtree" in name:
        return "Red-Black Tree$^*$"
    else:
        return name


if __name__ == "__main__":
    list_stats = []
    tree_stats = []
    stlc_stats = []
    for benchmark_dir in os.listdir(working_dir):
        if "combined_stlc_gen" in benchmark_dir or "excess" in benchmark_dir:
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

    def add_midrules_to_table(latex_table, stats):
        lines = latex_table.split("\n")
        result_lines = []

        # Track the current benchmark name to know when to add midrules
        current_benchmark_name = None
        current_section = None  # 'list' or 'tree'
        in_data_section = False

        for i, line in enumerate(lines):
            # Check if we're in the data section (after the first \hline)
            if "\\hline" in line and not in_data_section:
                in_data_section = True
                result_lines.append(line)
                continue
            elif "\\hline" in line and in_data_section:
                # This is the closing \hline, don't add midrule before it
                result_lines.append(line)
                continue
            elif "\\end{tabular}" in line:
                result_lines.append(line)
                continue

            # Look for data rows (not header, hline, or end tabular)
            if (
                in_data_section
                and line.strip()
                and not line.strip().startswith("\\")
                and "&" in line
                and "benchmark" not in line.lower()
            ):

                # Extract the name field (first column)
                name_part = line.split("&")[0].strip()

                # Determine the base benchmark name and section
                benchmark_name = None
                section = None

                if any(
                    x in name_part.lower()
                    for x in [
                        "sized list",
                        "even list",
                        "sorted list",
                        "duplicate list",
                        "unique list",
                    ]
                ):
                    section = "list"
                    if "sized list" in name_part.lower():
                        benchmark_name = "sized_list"
                    elif "even list" in name_part.lower():
                        benchmark_name = "even_list"
                    elif "sorted list" in name_part.lower():
                        benchmark_name = "sorted_list"
                    elif "duplicate list" in name_part.lower():
                        benchmark_name = "duplicate_list"
                    elif "unique list" in name_part.lower():
                        benchmark_name = "unique_list"
                elif any(
                    x in name_part.lower()
                    for x in ["red-black tree", "bst", "sized tree", "complete tree"]
                ):
                    section = "tree"
                    if "red-black tree" in name_part.lower():
                        benchmark_name = "rbtree"
                    elif "bst" in name_part.lower():
                        benchmark_name = "bst"
                    elif "sized tree" in name_part.lower():
                        benchmark_name = "sized_tree"
                    elif "complete tree" in name_part.lower():
                        benchmark_name = "complete_tree"
                elif "stlc" in name_part.lower():
                    section = "stlc"
                    benchmark_name = "stlc"
                elif name_part.isdigit() or name_part == "sketch":
                    # This is a continuation of the previous benchmark
                    benchmark_name = current_benchmark_name
                    section = current_section

                # Add \midrule and \hline when transitioning from list to tree section
                if (
                    section != current_section
                    and current_section == "list"
                    and section == "tree"
                ):
                    result_lines.append("\\midrule")
                    result_lines.append("\\hline")
                # Add midrule when benchmark name changes within the same section
                elif (
                    benchmark_name != current_benchmark_name
                    and current_benchmark_name is not None
                    and benchmark_name is not None
                    and section == current_section
                ):
                    result_lines.append("\\midrule")

                current_benchmark_name = benchmark_name
                current_section = section

            result_lines.append(line)

        return "\n".join(result_lines)

    def fix_latex_escaping(latex_table):
        """Fix the escaped LaTeX symbols that tabulate creates"""
        # Fix escaped backslashes in math mode
        latex_table = latex_table.replace("\\textbackslash{}", "\\")

        # Fix escaped curly braces
        latex_table = latex_table.replace("\\{", "{")
        latex_table = latex_table.replace("\\}", "}")

        # Fix escaped dollar signs
        latex_table = latex_table.replace("\\$", "$")

        # Fix escaped carets
        latex_table = latex_table.replace("\\^{}", "^")

        return latex_table

    # Combine list and tree stats into one table, keep STLC separate
    main_stats = []

    # Add list benchmarks first
    main_stats.extend(list_stats)

    # Add tree benchmarks
    main_stats.extend(tree_stats)

    # Create custom headers with shorter names
    headers = {
        "name": "Benchmark",
        "#Holes": "#Holes",
        "Repair Size": "Repair Size",
        "#Queries": "#Queries",
        "#Terms": "#Terms",
        "Abduction Time(s)": "Abduction (s)",
        "Synthesis Time(s)": "Synthesis (s)",
        "Total Time(s)": "Total Time(s)",
    }

    # Print main table (lists and trees)
    if main_stats:
        latex_table = tabulate(
            main_stats, headers=headers, tablefmt="latex", stralign="right"
        )

        # Replace the default tabular definition with custom column specification
        latex_table = latex_table.replace(
            "\\begin{tabular}{rrrrrrrr}", "\\begin{tabular}{r|rr|rrrrr}"
        )

        # Add midrules between different benchmark types
        latex_table = add_midrules_to_table(latex_table, main_stats)

        # Fix the escaped LaTeX symbols
        latex_table = fix_latex_escaping(latex_table)

        print(latex_table)

    # Print STLC table separately
    if stlc_stats:
        print("\n% STLC Benchmarks:")
        latex_table = tabulate(
            stlc_stats, headers=headers, tablefmt="latex", stralign="right"
        )

        # Replace the default tabular definition with custom column specification
        latex_table = latex_table.replace(
            "\\begin{tabular}{rrrrrrrr}", "\\begin{tabular}{r|rr|rrrrr}"
        )

        # Add midrules between different benchmark types
        latex_table = add_midrules_to_table(latex_table, stlc_stats)

        # Fix the escaped LaTeX symbols
        latex_table = fix_latex_escaping(latex_table)

        print(latex_table)
