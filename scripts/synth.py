import sys
import os
import re
from pathlib import Path

from runner import invoc_cmd

cmd_prefix = ["dune", "exec", "Cobb", "--no-buffer", "--"]
config_file = "meta-config.json"
working_dir = "underapproximation_type"
verbose = True


""" def run_synthesis_aux(meta_config_file, f):
    cmd = cmd_prefix + ["synthesis", meta_config_file, f]
    invoc_cmd(verbose, cmd, None) """


def run_synthesis_aux(file_name: str):
    cmd = cmd_prefix + ["synthesis", file_name]
    invoc_cmd(verbose, cmd, None, cwd=None)


def run_synthesis(dir_str: str):
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

                filename = dir_str + "/" + filename
                res = pool.apply_async(run_synthesis_aux, args=(filename,))
                multiple_res.append(res)

        [res.get() for res in multiple_res]


if __name__ == "__main__":
    dir_str = sys.argv[1]

    directory = Path(dir_str)
    assert directory.is_dir()

    working_dir = Path(working_dir)
    assert working_dir.is_dir()

    assert directory.is_relative_to(working_dir)
    os.chdir(working_dir)
    directory = os.path.relpath(directory, working_dir)

    run_synthesis(directory)
