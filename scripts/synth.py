import sys
import argparse
import os
import subprocess
import shutil
import locale
import re
from pathlib import Path

cmd_prefix = ["dune", "exec", "Cobb", "--no-buffer", "--"]
config_file = "meta-config.json"
workdir = "underapproximation_type"
verbose = True

my_env = os.environ.copy()
# "DUNE_CONFIG__GLOBAL_LOCK=disabled",
my_env["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"


def invoc_cmd(verbose, cmd, output_file, cwd=None):
    if output_file is not None:
        # print("{}:{}".format(output_file, type(output_file)))
        if verbose:
            print(" ".join(cmd + [">>", output_file]))
        with open(output_file, "a+") as ofile:
            try:
                subprocess.run(cmd, cwd=cwd, env=my_env, stdout=ofile)
            except subprocess.CalledProcessError as e:
                print(e.output)
                raise e
    else:
        if verbose:
            print(" ".join(cmd))
        try:
            subprocess.run(cmd, cwd=cwd, env=my_env)
        except subprocess.CalledProcessError as e:
            print(e.output)
            raise e


""" def run_synthesis_aux(meta_config_file, f):
    cmd = cmd_prefix + ["synthesis", meta_config_file, f]
    invoc_cmd(verbose, cmd, None) """


def run_synthesis_aux(dir_str, f):
    cmd = cmd_prefix + ["synthesis", dir_str, f]
    invoc_cmd(verbose, cmd, None, cwd=None)


def run_synthesis(dir_str):
    meta_config_file = "{}/{}".format(dir_str, config_file)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                run_synthesis(pp)
    else:
        from multiprocessing import Pool

        pool = Pool()

        multiple_res = []
        for filename in os.listdir(dir_str):
            matches = re.search(r"prog[0-9]+\.ml$", filename, re.MULTILINE)
            if matches:
                # run_synthesis_aux(meta_config_file, "{}/{}".format(dir_str,
                # filename))
                res = pool.apply_async(run_synthesis_aux, args=(dir_str, filename))
                multiple_res.append(res)

        [res.get() for res in multiple_res]


if __name__ == "__main__":
    dir_str = sys.argv[1]

    directory = Path(dir_str)
    assert directory.is_dir()

    working_dir = Path(workdir)
    assert working_dir.is_dir()

    assert directory.is_relative_to(working_dir)
    os.chdir(working_dir)
    directory = os.path.relpath(directory, working_dir)

    run_synthesis(directory)
