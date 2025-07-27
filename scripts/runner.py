import os
import sys
import subprocess
from pathlib import Path

my_env = os.environ.copy()
my_env["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"


def rescode_non_zero(res):
    return res.returncode != 0


def invoc_cmd(
    verbose, cmd, check_res, output_file=None, capture_output=False, cwd=None
):
    if output_file is not None:
        # print("{}:{}".format(output_file, type(output_file)))
        if verbose:
            print(" ".join(cmd + [">>", output_file]))
        with open(output_file, "a+") as ofile:
            try:
                res = subprocess.run(
                    cmd,
                    cwd=cwd,
                    capture_output=capture_output,
                    env=my_env,
                    stdout=ofile,
                    stderr=subprocess.PIPE,  # Capture stderr separately for error reporting
                )
                if check_res(res):
                    # Print detailed error information before raising exception
                    print(
                        f"Command failed with return code {res.returncode}: {' '.join(cmd)}",
                        file=sys.stderr,
                    )
                    if res.stderr:
                        stderr_output = (
                            res.stderr.decode()
                            if isinstance(res.stderr, bytes)
                            else res.stderr
                        )
                        print(f"Error output: {stderr_output}", file=sys.stderr)
                    raise subprocess.CalledProcessError(
                        res.returncode, cmd, stderr=res.stderr
                    )
            except subprocess.CalledProcessError as e:
                # Re-raise the exception - error details already printed above
                raise e
    else:
        if verbose:
            print(" ".join(cmd))
        try:
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, env=my_env)
            if check_res(res):
                # Print detailed error information before raising exception
                print(
                    f"Command failed with return code {res.returncode}: {' '.join(cmd)}",
                    file=sys.stderr,
                )
                if res.stderr:
                    stderr_output = (
                        res.stderr.decode()
                        if isinstance(res.stderr, bytes)
                        else res.stderr
                    )
                    print(f"Error output: {stderr_output}", file=sys.stderr)
                if res.stdout:
                    stdout_output = (
                        res.stdout.decode()
                        if isinstance(res.stdout, bytes)
                        else res.stdout
                    )
                    print(f"Standard output: {stdout_output}", file=sys.stderr)
                raise subprocess.CalledProcessError(
                    res.returncode, cmd, res.stdout, res.stderr
                )
        except subprocess.CalledProcessError as e:
            # Re-raise the exception - error details already printed above
            raise e


def run_for_dir_from_cli(workdir, f):
    dir_str = sys.argv[1]

    directory = Path(dir_str)
    assert directory.is_dir()

    working_dir = Path(workdir)
    assert working_dir.is_dir()

    assert directory.is_relative_to(working_dir)
    os.chdir(working_dir)
    directory = os.path.relpath(directory, working_dir)

    f(directory)
