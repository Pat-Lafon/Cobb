import os
import re
import csv
from typing import List, Dict, Tuple


class BenchmarkDataProcessor:
    """
    A class to handle the common data processing tasks for benchmark results.
    This includes reading CSV files, processing benchmark data, and organizing results.
    """

    def __init__(self, working_dir: str = "underapproximation_type/data/validation"):
        self.working_dir = working_dir
        self.results_file_regex = r"prog[0-9]+\.ml.result.csv$"

    def fix_name(self, name: str) -> str:
        """Convert benchmark directory names to readable format."""
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

    def fix_name_latex(self, name: str) -> str:
        """Convert benchmark directory names to LaTeX format."""
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

    def read_benchmark_data(
        self, use_latex_names: bool = False
    ) -> Tuple[List[Dict], List[Dict], List[Dict]]:
        """
        Read and process all benchmark data from the working directory.

        Args:
            use_latex_names: Whether to use LaTeX formatting for benchmark names

        Returns:
            Tuple of (list_stats, tree_stats, stlc_stats)
        """
        list_stats = []
        tree_stats = []
        stlc_stats = []

        name_formatter = self.fix_name_latex if use_latex_names else self.fix_name

        for benchmark_dir in os.listdir(self.working_dir):
            if (
                "combined_stlc_gen" in benchmark_dir
                or "excess" in benchmark_dir
                or "imprecise" in benchmark_dir
            ):
                continue

            b_path = f"{self.working_dir}/{benchmark_dir}"
            benchmark_stats = []

            if os.path.isdir(b_path):
                print(f"looking in {b_path}")
                d = os.listdir(b_path)
                d.sort()

                d = list(
                    filter(
                        lambda filename: re.search(
                            self.results_file_regex, filename, re.MULTILINE
                        ),
                        d,
                    )
                )

                for idx, filename in enumerate(d, start=1):
                    stats = {}
                    n = filename.split(".")[0].removeprefix("prog")
                    name = ""
                    if n == "1":
                        name = f"{name_formatter(benchmark_dir)} {n}"
                    elif idx == len(d) and not benchmark_dir.startswith("stlc"):
                        # Only non-STLC benchmarks can have sketch cases
                        name = "sketch"
                    else:
                        name = n
                    print(name)
                    stats["name"] = name

                    with open(f"{b_path}/{filename}", "r") as f:
                        reader = csv.DictReader(f)
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

            if benchmark_stats:
                if (
                    "list" in benchmark_dir
                    or "depthtree" in benchmark_dir
                    or "complete_tree" in benchmark_dir
                ):
                    list_stats += benchmark_stats
                elif "bst" in benchmark_dir or "rbtree" in benchmark_dir:
                    tree_stats += benchmark_stats
                else:
                    stlc_stats += benchmark_stats

        return list_stats, tree_stats, stlc_stats

    def sort_benchmarks(self, stats: List[Dict]) -> List[Dict]:
        """
        Sort benchmark statistics to ensure correct ordering while preserving benchmark groupings.
        """
        # Define the desired order for each benchmark type
        list_order = [
            "sized",
            "duplicate",
            "unique",
            "sorted",
            "even",
            "depth",
            "complete",
        ]
        tree_order = ["bst", "rbtree"]

        # Group stats by benchmark type
        grouped_stats = {}
        current_benchmark = None

        for stat in stats:
            name = stat["name"].lower()

            # Determine which benchmark this belongs to
            if "sized list" in name:
                current_benchmark = "sized"
            elif "duplicate list" in name:
                current_benchmark = "duplicate"
            elif "unique list" in name:
                current_benchmark = "unique"
            elif "sorted list" in name:
                current_benchmark = "sorted"
            elif "even list" in name:
                current_benchmark = "even"
            elif "bst" in name:
                current_benchmark = "bst"
            elif "sized tree" in name:
                current_benchmark = "depth"
            elif "complete tree" in name:
                current_benchmark = "complete"
            elif "red-black tree" in name:
                current_benchmark = "rbtree"
            # For numbered entries and sketches, use the last benchmark

            if current_benchmark:
                if current_benchmark not in grouped_stats:
                    grouped_stats[current_benchmark] = []
                grouped_stats[current_benchmark].append(stat)

        # Rebuild the list in the correct order
        ordered_stats = []

        # First add list benchmarks in order
        for benchmark in list_order:
            if benchmark in grouped_stats:
                ordered_stats.extend(grouped_stats[benchmark])

        # Then add tree benchmarks in order
        for benchmark in tree_order:
            if benchmark in grouped_stats:
                ordered_stats.extend(grouped_stats[benchmark])

        return ordered_stats

    def get_combined_main_stats(self, use_latex_names: bool = False) -> List[Dict]:
        """
        Get combined list and tree statistics, properly sorted.

        Args:
            use_latex_names: Whether to use LaTeX formatting for benchmark names

        Returns:
            Combined and sorted list of benchmark statistics
        """
        list_stats, tree_stats, _ = self.read_benchmark_data(use_latex_names)
        main_stats = list_stats + tree_stats
        return self.sort_benchmarks(main_stats)

    def get_all_stats(
        self, use_latex_names: bool = False
    ) -> Tuple[List[Dict], List[Dict], List[Dict]]:
        """
        Get all benchmark statistics organized as main (list only), tree (BST/RBTree), and STLC.

        Args:
            use_latex_names: Whether to use LaTeX formatting for benchmark names

        Returns:
            Tuple of (main_stats, tree_stats, stlc_stats)
        """
        list_stats, tree_stats, stlc_stats = self.read_benchmark_data(use_latex_names)
        main_stats = self.sort_benchmarks(list_stats)
        tree_stats = self.sort_benchmarks(tree_stats)
        return main_stats, tree_stats, stlc_stats
