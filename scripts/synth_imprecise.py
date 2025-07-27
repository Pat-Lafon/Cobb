#!/usr/bin/env python3
"""
Script to run all programs in an imprecise benchmark directory.
Usage: python scripts/synth_imprecise.py <benchmark_directory>
Example: python scripts/synth_imprecise.py underapproximation_type/data/validation/even_list_imprecise
"""

import sys
import os
import subprocess
import argparse


def run_imprecise_benchmark(benchmark_dir):
    """Run all programs in an imprecise benchmark directory."""
    if not os.path.isdir(benchmark_dir):
        print(f"Error: Directory {benchmark_dir} does not exist")
        return False

    # Find all prog* subdirectories
    prog_dirs = []
    for item in os.listdir(benchmark_dir):
        item_path = os.path.join(benchmark_dir, item)
        if os.path.isdir(item_path) and item.startswith("prog"):
            prog_dirs.append(item)

    if not prog_dirs:
        print(f"No program directories found in {benchmark_dir}")
        return False

    prog_dirs.sort()  # Sort for consistent ordering

    print(f"Found {len(prog_dirs)} programs in {benchmark_dir}")

    success_count = 0
    total_count = len(prog_dirs)

    for prog_dir in prog_dirs:
        prog_path = os.path.join(benchmark_dir, prog_dir)
        prog_file = f"{prog_dir}.ml"
        prog_file_path = os.path.join(prog_path, prog_file)
        meta_config_path = os.path.join(prog_path, "meta-config.json")

        # Check if required files exist
        if not os.path.exists(prog_file_path):
            print(f"Warning: {prog_file_path} not found, skipping")
            continue

        if not os.path.exists(meta_config_path):
            print(f"Warning: {meta_config_path} not found, skipping")
            continue

        print(f"Running {prog_dir}...")

        # Run the command - need to find the underapproximation_type directory
        # where the synthesis command expects to be run from
        underapprox_dir = None
        current_path = os.path.abspath(benchmark_dir)
        while current_path and current_path != "/":
            if os.path.basename(current_path) == "underapproximation_type":
                underapprox_dir = current_path
                break
            current_path = os.path.dirname(current_path)

        if not underapprox_dir:
            print(
                f"Error: Could not find underapproximation_type directory from {benchmark_dir}"
            )
            continue

        # Calculate relative path from underapproximation_type to the program file
        rel_prog_file_path = os.path.relpath(prog_file_path, underapprox_dir)

        cmd = [
            "dune",
            "exec",
            "../bin/main.exe",
            "--",
            "synthesis",
            rel_prog_file_path,
        ]

        try:
            result = subprocess.run(
                cmd, cwd=underapprox_dir, capture_output=True, text=True
            )

            if result.returncode == 0:
                success_count += 1
                print(f"  ✓ {prog_dir} succeeded")
            else:
                print(f"  ✗ {prog_dir} failed")
                if result.stderr:
                    print(f"    Error: {result.stderr.strip()}")
                if result.stdout:
                    print(f"    Output: {result.stdout.strip()}")
                # Stop on first failure
                print(f"Stopping on first failure. Error in {prog_dir}")
                return False

        except subprocess.CalledProcessError as e:
            print(f"  ✗ {prog_dir} failed with exception: {e}")
            print(f"Stopping on first failure. Error in {prog_dir}")
            return False
        except Exception as e:
            print(f"  ✗ {prog_dir} failed with unexpected error: {e}")
            print(f"Stopping on first failure. Error in {prog_dir}")
            return False

    print(f"\nResults: {success_count}/{total_count} programs succeeded")
    return success_count == total_count


def main():
    parser = argparse.ArgumentParser(
        description="Run all programs in an imprecise benchmark directory"
    )
    parser.add_argument(
        "benchmark_dir", help="Path to the imprecise benchmark directory"
    )

    args = parser.parse_args()

    success = run_imprecise_benchmark(args.benchmark_dir)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
