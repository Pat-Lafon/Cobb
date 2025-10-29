import os
from tabulate import tabulate, SEPARATING_LINE
from benchmark_data import BenchmarkDataProcessor


if __name__ == "__main__":
    # Initialize the data processor
    processor = BenchmarkDataProcessor()

    # Get all benchmark data with LaTeX formatting
    main_stats, tree_stats, stlc_stats = processor.get_all_stats(use_latex_names=True)
    # Combine main and tree stats for the main table
    combined_main_stats = main_stats + tree_stats

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
                    elif "duplicate list" in name_part.lower():
                        benchmark_name = "duplicate_list"
                    elif "unique list" in name_part.lower():
                        benchmark_name = "unique_list"
                    elif "sorted list" in name_part.lower():
                        benchmark_name = "sorted_list"
                    elif "even list" in name_part.lower():
                        benchmark_name = "even_list"
                elif any(
                    x in name_part.lower()
                    for x in ["red-black tree", "bst", "sized tree", "complete tree"]
                ):
                    section = "tree"
                    if "sized tree" in name_part.lower():
                        benchmark_name = "sized_tree"
                    elif "complete tree" in name_part.lower():
                        benchmark_name = "complete_tree"
                    elif "bst" in name_part.lower():
                        benchmark_name = "bst"
                    elif "red-black tree" in name_part.lower():
                        benchmark_name = "rbtree"
                elif "stlc" in name_part.lower():
                    section = "stlc"
                    benchmark_name = "stlc"
                elif name_part.isdigit() or name_part == "sketch":
                    # This is a continuation of the previous benchmark
                    benchmark_name = current_benchmark_name
                    section = current_section

                # Add special transitions for specific cases
                if (
                    section != current_section
                    and current_section == "list"
                    and section == "tree"
                ):
                    # Transition from list to tree section - use hhline
                    result_lines.append("  \\hhline{=|==|=====}")
                # Add hhline before Red-Black Tree (when transitioning from BST to Red-Black Tree)
                elif (
                    benchmark_name == "rbtree"
                    and current_benchmark_name == "bst"
                    and section == "tree"
                ):
                    # Special transition before Red-Black Tree
                    result_lines.append("  \\hhline{=|==|=====}")
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

    # Create output directory if it doesn't exist
    output_dir = "data"
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, "benchmark_results.tex")

    # Collect all LaTeX output
    latex_output = []

    # Generate main table (lists and trees)
    if combined_main_stats:
        latex_table = tabulate(
            combined_main_stats, headers=headers, tablefmt="latex", stralign="right"
        )

        # Replace the default tabular definition with custom column specification
        latex_table = latex_table.replace(
            "\\begin{tabular}{rrrrrrrr}", "\\begin{tabular}{r|rr|rrrrr}"
        )

        # Add midrules between different benchmark types
        latex_table = add_midrules_to_table(latex_table, combined_main_stats)

        # Fix the escaped LaTeX symbols
        latex_table = fix_latex_escaping(latex_table)

        latex_output.append("% Main Benchmarks (Lists and Trees):")
        latex_output.append(latex_table)

    # Generate STLC table separately
    if stlc_stats:
        latex_output.append("\n% STLC Benchmarks:")
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

        latex_output.append(latex_table)

    # Write all LaTeX output to file
    with open(output_file, "w") as f:
        f.write("\n".join(latex_output))

    print(f"LaTeX tables written to: {output_file}")

    # Also print to stdout for backward compatibility
    print("\n".join(latex_output))
