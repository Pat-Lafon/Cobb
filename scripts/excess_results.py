import os
import re
import csv
from tabulate import tabulate, SEPARATING_LINE

# Based on results.py structure, adapted for comparing excess vs non-excess benchmarks

working_dir = "underapproximation_type/data/validation"
results_file_regex = r"prog[0-9]+\.ml.result.csv$"


def fix_name(name):
    """Convert benchmark directory names to human-readable format"""
    # Remove '_excess' suffix for display purposes
    base_name = name.replace("_excess", "")

    if "sized" in base_name:
        return "Sized List"
    elif "even" in base_name:
        return "Even List"
    elif "sorted" in base_name:
        return "Sorted List"
    elif "bst" in base_name:
        return "BST"
    elif "duplicate" in base_name:
        return "Duplicate List"
    elif "unique" in base_name:
        return "Unique List"
    elif "depth" in base_name:
        return "Sized Tree"
    elif "complete" in base_name:
        return "Complete Tree"
    elif "rbtree" in base_name:
        return "Red-Black Tree"
    else:
        return base_name


def find_benchmark_pairs():
    """
    Find pairs of benchmark directories (base and _excess versions)
    Returns a list of tuples: (base_dir, excess_dir)
    """
    pairs = []

    # List all directories in working_dir
    for item in os.listdir(working_dir):
        item_path = os.path.join(working_dir, item)
        if os.path.isdir(item_path) and item.endswith("_excess"):
            # Found an excess directory
            base_name = item.replace("_excess", "")
            base_path = os.path.join(working_dir, base_name)

            # Check if corresponding base directory exists
            if os.path.isdir(base_path):
                pairs.append((base_name, item))

    return pairs


def _parse_stats_from_csv(csv_path):
    """
    Helper function to parse statistics from a CSV file

    Returns: dict with statistics from the CSV file
    """
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


def _get_program_stats(benchmark_dir, get_last_file=True):
    """
    Unified function to extract statistics from benchmark directories

    Args:
        benchmark_dir: Directory name (relative to working_dir)
        get_last_file: If True, get the last (highest numbered) file. If False, get first file.

    Returns: dict with statistics from the program
    """
    b_path = "{}/{}".format(working_dir, benchmark_dir)

    # Get all .result.csv files
    files = os.listdir(b_path)
    result_files = list(
        filter(
            lambda filename: re.search(results_file_regex, filename, re.MULTILINE),
            files,
        )
    )

    if not result_files:
        raise FileNotFoundError(f"No .result.csv files found in {b_path}")

    # Select target file based on strategy
    result_files.sort()
    target_file = result_files[-1] if get_last_file else result_files[0]

    # Parse and return stats
    return _parse_stats_from_csv("{}/{}".format(b_path, target_file))


def _count_components(benchmark_dir):
    """
    Count the number of components in a benchmark directory

    Returns: int - number of components
    """
    b_path = "{}/{}".format(working_dir, benchmark_dir)
    components_file = "{}/components.txt".format(b_path)

    try:
        with open(components_file, "r") as f:
            # Count non-empty lines in components.txt
            components = [line.strip() for line in f if line.strip()]
            component_count = len(components)

            if component_count == 0:
                raise ValueError(
                    f"No components found in {components_file} - file is empty or contains only whitespace"
                )

            return component_count
    except FileNotFoundError:
        raise FileNotFoundError(f"components.txt not found in {b_path}")
    except Exception as e:
        raise ValueError(f"Error reading components.txt in {b_path}: {e}")


def get_synthesized_program_stats(base_dir):
    """
    Extract statistics for the synthesized program from the base benchmark directory
    The synthesized program is typically the last numbered program or named 'sketch'

    Returns: dict with statistics from the synthesized program
    """
    return _get_program_stats(base_dir, get_last_file=True)


def get_excess_program_stats(excess_dir):
    """
    Extract statistics for the single program in the excess benchmark directory

    Returns: dict with statistics from the excess program
    """
    return _get_program_stats(excess_dir, get_last_file=False)


def compare_stats(base_stats, excess_stats, benchmark_name, base_dir, excess_dir):
    """
    Compare statistics between base synthesized program and excess program

    Returns: dict with comparison metrics
    """
    if base_stats is None or excess_stats is None:
        raise ValueError(
            f"Missing stats for {benchmark_name}: base={base_stats}, excess={excess_stats}"
        )

    def safe_numeric_convert(value, force_int=False):
        """Convert string values to numeric, handle empty/missing values"""
        if value is None or value == "" or value == "N/A":
            return 0
        try:
            if force_int:
                return int(
                    float(value)
                )  # Convert via float first to handle "99.0" -> 99
            else:
                return float(value)
        except ValueError:
            return 0

    def calculate_ratio(excess_val, base_val):
        """Calculate ratio, handling division by zero"""
        if base_val == 0:
            return float("inf") if excess_val > 0 else 1.0
        return excess_val / base_val

    def calculate_percentage_change(excess_val, base_val):
        """Calculate percentage change from base to excess"""
        if base_val == 0:
            return float("inf") if excess_val > 0 else 0.0
        return ((excess_val - base_val) / base_val) * 100

    # Focus on metrics that are likely to change significantly
    key_metrics = ["#Queries", "#Terms", "Synthesis Time(s)"]
    integer_metrics = {"#Queries", "#Terms"}  # These should be integers

    comparison = {
        "Benchmark": benchmark_name,
    }

    # Add component counts
    base_components = _count_components(base_dir)
    excess_components = _count_components(excess_dir)
    comparison["Base Components"] = base_components
    comparison["Δ Components"] = excess_components - base_components

    # Add base values and increases for key metrics
    for metric in key_metrics:
        is_integer = metric in integer_metrics
        base_val = safe_numeric_convert(base_stats[metric], force_int=is_integer)
        excess_val = safe_numeric_convert(excess_stats[metric], force_int=is_integer)
        increase = excess_val - base_val  # Positive = overhead, Negative = improvement

        comparison[f"Base {metric}"] = base_val
        comparison[f"Δ {metric}"] = increase

    return comparison


def format_comparison_table(comparison_data, category_name):
    """
    Format the comparison data into a CSV file and print a simple table
    """
    if not comparison_data:
        raise ValueError(f"No comparison data provided for {category_name} benchmarks!")

    # Ensure data directory exists
    os.makedirs("data", exist_ok=True)

    # Generate CSV filename in data directory
    csv_filename = f"data/excess_comparison_{category_name.lower()}.csv"

    # Format floating point values to 2 decimal places for CSV
    formatted_data = []
    for row in comparison_data:
        formatted_row = {}
        for key, value in row.items():
            if isinstance(value, float):
                formatted_row[key] = round(value, 2)
            else:
                formatted_row[key] = value
        formatted_data.append(formatted_row)

    # Write to CSV
    with open(csv_filename, "w", newline="") as csvfile:
        fieldnames = formatted_data[0].keys()
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(formatted_data)

    print(f"Results written to {csv_filename}")

    # Print simple table for visualization
    print(tabulate(formatted_data, headers="keys", tablefmt="grid", floatfmt=".2f"))

    return csv_filename


def categorize_benchmarks(benchmark_pairs):
    """
    Categorize benchmark pairs into lists and trees (ignoring STLC benchmarks)
    """
    list_pairs = []
    tree_pairs = []

    for base_dir, excess_dir in benchmark_pairs:
        if "list" in base_dir:
            list_pairs.append((base_dir, excess_dir))
        elif "tree" in base_dir or "bst" in base_dir:
            tree_pairs.append((base_dir, excess_dir))
        # Ignore STLC benchmarks (anything that doesn't match list or tree patterns)

    return list_pairs, tree_pairs


if __name__ == "__main__":
    print("=== Excess vs Synthesized Program Comparison ===")

    # NOTE: This is a skeleton/plan - functions need to be implemented
    # Current functions return None/pass, so execution will fail until implemented

    # Step 1: Find all benchmark pairs (base + excess)
    benchmark_pairs = find_benchmark_pairs()
    print(f"Found {len(benchmark_pairs)} benchmark pairs")

    # Step 2: Categorize benchmarks
    list_pairs, tree_pairs = categorize_benchmarks(benchmark_pairs)

    # Step 3: Process each category
    for category_name, pairs in [
        ("Lists", list_pairs),
        ("Trees", tree_pairs),
    ]:
        if not pairs:
            raise ValueError(
                f"No {category_name.lower()} benchmark pairs found! Expected directories with 'list'/'tree'/'bst' patterns."
            )

        print(f"\n=== {category_name} Benchmarks ===")
        comparison_data = []

        for base_dir, excess_dir in pairs:
            benchmark_name = fix_name(base_dir)

            # Get statistics from both versions
            base_stats = get_synthesized_program_stats(base_dir)
            excess_stats = get_excess_program_stats(excess_dir)

            # Compare and format
            comparison = compare_stats(
                base_stats, excess_stats, benchmark_name, base_dir, excess_dir
            )

            comparison_data.append(comparison)

        # Generate and print comparison table
        csv_file = format_comparison_table(comparison_data, category_name)
        print(f"CSV file generated: {csv_file}")

    print("\n=== Summary ===")
    # TODO: Add overall summary statistics
    # - Average improvements/degradations
    # - Best/worst performing benchmarks
    # - Overall trends
