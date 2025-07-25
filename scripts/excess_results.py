import os
import re
import csv
from pathlib import Path
from typing import List, Tuple, Dict, Any
from tabulate import tabulate

# Configuration constants
WORKING_DIR = "underapproximation_type/data/validation"
RESULTS_FILE_REGEX = r"prog[0-9]+\.ml.result.csv$"
EXCESS_SUFFIX = "_excess"
OUTPUT_DIR = "data"

# CSV column mappings
CSV_COLUMN_MAPPING = {
    "#Holes": " #Holes",
    "Repair Size": " Repair Size",
    "#Queries": " Queries",
    "#Terms": " #Terms",
    "Abduction Time(s)": " Abd Time",
    "Synthesis Time(s)": " Synth Time",
    "Total Time(s)": " Total Time",
}

# Benchmark name mappings
BENCHMARK_NAME_MAP = {
    "sized": "Sized List",
    "even": "Even List",
    "sorted": "Sorted List",
    "bst": "BST",
    "duplicate": "Duplicate List",
    "unique": "Unique List",
    "depth": "Sized Tree",
    "complete": "Complete Tree",
    "rbtree": "Red-Black Tree",
}


def fix_name(name: str) -> str:
    """Convert benchmark directory names to human-readable format"""
    base_name = name.replace(EXCESS_SUFFIX, "")

    # Return first match or original name
    return next(
        (
            display_name
            for key, display_name in BENCHMARK_NAME_MAP.items()
            if key in base_name
        ),
        base_name,
    )


def find_benchmark_pairs() -> List[Tuple[str, str]]:
    """Find pairs of benchmark directories (base and _excess versions)"""
    working_path = Path(WORKING_DIR)

    pairs = []
    for item in working_path.iterdir():
        if item.is_dir() and item.name.endswith(EXCESS_SUFFIX):
            base_name = item.name.replace(EXCESS_SUFFIX, "")
            base_path = working_path / base_name

            if base_path.is_dir():
                pairs.append((base_name, item.name))

    return pairs


def _parse_stats_from_csv(csv_path: str) -> Dict[str, str]:
    """Helper function to parse statistics from a CSV file"""
    stats = {}
    with open(csv_path, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            stats["#Holes"] = row[" #Holes"]
            stats["Repair Size"] = row[" Repair Size"]
            stats["#Queries"] = row[" Queries"]
            stats["#Terms"] = row[" #Terms"]
            stats["Abduction Time(s)"] = row[" Abd Time"]
            stats["Synthesis Time(s)"] = row[" Synth Time"]
            stats["Total Time(s)"] = row[" Total Time"]
            break  # Only process first (and only) row
    return stats


def _get_program_stats(
    benchmark_dir: str, get_last_file: bool = True
) -> Dict[str, str]:
    """Extract statistics from benchmark directories"""
    b_path = Path(WORKING_DIR) / benchmark_dir

    # Get all .result.csv files and sort them
    result_files = sorted(
        [
            f
            for f in b_path.iterdir()
            if f.is_file() and re.search(RESULTS_FILE_REGEX, f.name)
        ]
    )

    if not result_files:
        raise FileNotFoundError(f"No .result.csv files found in {b_path}")

    # Select first or last file
    target_file = result_files[-1] if get_last_file else result_files[0]

    return _parse_stats_from_csv(str(target_file))


def _count_components(benchmark_dir: str) -> int:
    """Count the number of components in a benchmark directory"""
    components_file = Path(WORKING_DIR) / benchmark_dir / "components.txt"

    try:
        components = [
            line.strip()
            for line in components_file.read_text().splitlines()
            if line.strip()
        ]
        if not components:
            raise ValueError(f"No components found in {components_file}")
        return len(components)
    except FileNotFoundError:
        raise FileNotFoundError(f"components.txt not found in {components_file.parent}")
    except Exception as e:
        raise ValueError(f"Error reading {components_file}: {e}")


def _safe_numeric_convert(value: Any, force_int: bool = False) -> float:
    """Convert string values to numeric, handle empty/missing values"""
    if value is None or value == "" or value == "N/A":
        return 0.0
    try:
        if force_int:
            return float(
                int(float(value))
            )  # Convert via float first to handle "99.0" -> 99
        else:
            return float(value)
    except (ValueError, TypeError):
        return 0.0


def _format_metric_with_percentage(
    base_val: float, excess_val: float, is_time: bool = False
) -> str:
    """Format a metric value with percentage change"""
    if base_val <= 0:
        return f"{excess_val:.2f}" if is_time else f"{int(excess_val)}"

    pct_change = ((excess_val - base_val) / base_val) * 100
    if is_time:
        return f"{excess_val:.2f} ({pct_change:+.1f}\\%)"
    else:
        return f"{int(excess_val)} ({pct_change:+.1f}\\%)"


def compare_stats(
    base_stats: Dict[str, str],
    excess_stats: Dict[str, str],
    benchmark_name: str,
    base_dir: str,
    excess_dir: str,
) -> Dict[str, str]:
    """Compare statistics between base synthesized program and excess program"""
    if base_stats is None or excess_stats is None:
        raise ValueError(
            f"Missing stats for {benchmark_name}: base={base_stats}, excess={excess_stats}"
        )

    # Component counts
    base_components = _count_components(base_dir)
    excess_components = _count_components(excess_dir)
    extra_components = excess_components - base_components
    components_str = f"{excess_components} ({extra_components:+d})"

    # Process key metrics with their formatting
    metrics = {}
    for metric, is_integer in [
        ("#Queries", True),
        ("#Terms", True),
        ("Synthesis Time(s)", False),
    ]:
        base_val = _safe_numeric_convert(base_stats[metric], force_int=is_integer)
        excess_val = _safe_numeric_convert(excess_stats[metric], force_int=is_integer)
        is_time = metric == "Synthesis Time(s)"
        metrics[metric] = _format_metric_with_percentage(base_val, excess_val, is_time)

    return {
        "Benchmark": benchmark_name,
        "Components": components_str,
        "Queries": metrics["#Queries"],
        "Terms": metrics["#Terms"],
        "Time": metrics["Synthesis Time(s)"],
    }


def format_comparison_table(
    comparison_data: List[Dict[str, str]], category_name: str
) -> str:
    """Format the comparison data into a CSV file and print a simple table"""
    if not comparison_data:
        raise ValueError(f"No comparison data provided for {category_name} benchmarks!")

    # Ensure output directory exists
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    # Generate CSV filename in output directory
    csv_filename = f"{OUTPUT_DIR}/excess_comparison_{category_name.lower()}.csv"

    # Write to CSV
    with open(csv_filename, "w", newline="") as csvfile:
        if comparison_data:  # Ensure we have data
            writer = csv.DictWriter(csvfile, fieldnames=comparison_data[0].keys())
            writer.writeheader()
            writer.writerows(comparison_data)

    print(f"Results written to {csv_filename}")

    # Print table for visualization
    print(tabulate(comparison_data, headers="keys", tablefmt="grid"))

    return csv_filename


def process_benchmark_pair(base_dir: str, excess_dir: str) -> Dict[str, str]:
    """Process a single benchmark pair and return comparison metrics"""
    benchmark_name = fix_name(base_dir)
    base_stats = _get_program_stats(base_dir, get_last_file=True)
    excess_stats = _get_program_stats(excess_dir, get_last_file=False)
    return compare_stats(base_stats, excess_stats, benchmark_name, base_dir, excess_dir)


def main() -> None:
    """Main execution function"""
    print("=== Excess vs Synthesized Program Comparison ===")

    # Find benchmark pairs and filter for list/tree types
    benchmark_pairs = find_benchmark_pairs()
    print(f"Found {len(benchmark_pairs)} benchmark pairs")

    # Categorize and combine into one list
    list_pairs = [(base, excess) for base, excess in benchmark_pairs if "list" in base]
    tree_pairs = [
        (base, excess)
        for base, excess in benchmark_pairs
        if "tree" in base or "bst" in base
    ]
    all_pairs = list_pairs + tree_pairs

    if not all_pairs:
        raise ValueError(
            "No benchmark pairs found! Expected directories with 'list'/'tree'/'bst' patterns."
        )

    print(f"\n=== Combined Benchmarks ===")
    comparison_data = []

    # Process each benchmark pair
    for base_dir, excess_dir in all_pairs:
        try:
            comparison = process_benchmark_pair(base_dir, excess_dir)
            comparison_data.append(comparison)
        except Exception as e:
            print(f"Warning: Failed to process {fix_name(base_dir)}: {e}")

    # Generate results
    csv_file = format_comparison_table(comparison_data, "combined")
    print(f"CSV file generated: {csv_file}")
    print(f"\n=== Summary ===")
    print(
        f"Successfully processed {len(comparison_data)} out of {len(all_pairs)} benchmark pairs"
    )


if __name__ == "__main__":
    main()
