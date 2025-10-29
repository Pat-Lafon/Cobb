#!/usr/bin/env python3

import matplotlib.pyplot as plt
import os
from benchmark_data import BenchmarkDataProcessor

# Global constants
CHARTS_OUTPUT_DIR = "charts"


def create_consolidated_chart(all_stats_data, chart_title, output_file):
    """
    Create a consolidated bar chart showing total time for sketch cases of benchmarks.
    Uses logarithmic scale and excludes STLC benchmarks.

    Args:
        all_stats_data: List of all benchmark statistics
        chart_title: Title for the chart
        output_file: Path to save the chart
    """
    # Filter data to use only sketch cases of regular benchmarks (ignore STLC entirely)
    benchmark_data = []
    current_benchmark = None

    for stat in all_stats_data:
        name = stat["name"]

        # Check if this is a benchmark type name (starts new benchmark group)
        if not name.isdigit() and name != "sketch":
            current_benchmark = name
            # Skip STLC benchmarks entirely
            if name.startswith("stlc"):
                current_benchmark = None
        elif name == "sketch" and current_benchmark:
            # Use sketch case for regular benchmarks only
            total_time = float(stat["Total Time(s)"])
            # Clean up benchmark name by removing the " 1" suffix
            clean_name = (
                current_benchmark.replace(" 1", "")
                if current_benchmark.endswith(" 1")
                else current_benchmark
            )
            benchmark_data.append({"name": clean_name, "total_time": total_time})

    if not benchmark_data:
        print("No data found for chart generation")
        return

    # Debug: Print collected benchmark data
    print(f"Collected {len(benchmark_data)} sketch benchmarks for the chart:")
    for item in benchmark_data:
        print(f"  {item['name']}: {item['total_time']:.2f}s")

    # Sort data by total time (height) in ascending order
    benchmark_data.sort(key=lambda x: x["total_time"])

    # Extract names and times for plotting
    names = [item["name"] for item in benchmark_data]
    times = [item["total_time"] for item in benchmark_data]

    # Create the plot
    fig, ax = plt.subplots(figsize=(14, 8))

    # Create bars with a single color scheme
    bar_color = "#2E86AB"  # Blue color for all bars
    x_positions = range(len(names))

    bars = ax.bar(
        x_positions,
        times,
        color=bar_color,
        alpha=0.8,
        edgecolor="black",
        linewidth=0.5,
        width=0.6,
    )

    # Use logarithmic scale for y-axis
    ax.set_yscale("log")
    ax.set_ylabel("Total Time(s)", fontsize=24)
    ax.set_title(chart_title, fontsize=32, fontweight="bold")

    # Increase y-axis tick label font size
    ax.tick_params(axis="y", labelsize=24)

    # Set x-axis labels
    ax.set_xticks(x_positions)
    ax.set_xticklabels(names, rotation=45, ha="right", fontsize=20)

    # Add grid for better readability with log scale
    ax.grid(True, alpha=0.3, axis="y")

    # Add horizontal line at 1 minute (60 seconds) to emphasize the threshold
    ax.axhline(y=60, color="red", linestyle="--", linewidth=2, alpha=0.7)

    # Add text label for the 1-minute line
    ax.text(
        len(names) * 0.02,
        60 * 1.15,
        "1 minute",
        fontsize=24,
        color="red",
        fontweight="bold",
        verticalalignment="bottom",
    )

    # Set tight x-axis limits
    ax.set_xlim(-0.5, len(names) - 0.5)

    plt.tight_layout()

    # Save the plot
    plt.savefig(output_file, dpi=300, bbox_inches="tight")
    print(f"Chart saved to: {output_file}")
    plt.close()


def main():
    # Hard coded data directory path
    data_dir = "underapproximation_type/data/validation"

    # Process the data
    processor = BenchmarkDataProcessor(data_dir)
    main_stats, tree_stats, stlc_stats = processor.get_all_stats()

    # Combine only main and tree benchmarks (exclude STLC)
    all_stats = main_stats + tree_stats

    # Always save files to charts directory
    os.makedirs(CHARTS_OUTPUT_DIR, exist_ok=True)
    consolidated_output = os.path.join(
        CHARTS_OUTPUT_DIR, "consolidated_benchmarks_chart.png"
    )

    # Create single consolidated chart with sketch cases only
    create_consolidated_chart(
        all_stats, "Benchmark Total Times (Sketch Cases Only)", consolidated_output
    )

    print("Consolidated chart generation complete!")


if __name__ == "__main__":
    main()
