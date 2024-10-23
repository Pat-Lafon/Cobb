import os
import re

from runner import invoc_cmd, run_for_dir_from_cli, rescode_non_zero

cmd_prefix = "dune exec Cobb --no-buffer -- abduction".split(" ")
config_file = "meta-config.json"
working_dir = "underapproximation_type"
verbose = True


def run_abduction_aux(cmd):
    invoc_cmd(verbose, cmd, rescode_non_zero, None, cwd=None)


def run_abduction(dir_str: str):
    meta_config_file = "{}/{}".format(dir_str, config_file)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                run_abduction(pp)
    else:
        from multiprocessing import Pool

        pool = Pool()

        multiple_res = []
        for filename in os.listdir(dir_str):
            matches = re.search(r"prog[0-9]*\.ml$", filename, re.MULTILINE)
            if matches:
                filename = dir_str + "/" + filename
                cmd = cmd_prefix + [filename]
                res = pool.apply_async(run_abduction_aux, args=[cmd])
                multiple_res.append(res)

        [res.get() for res in multiple_res]


if __name__ == "__main__":
    run_for_dir_from_cli(working_dir, run_abduction)
