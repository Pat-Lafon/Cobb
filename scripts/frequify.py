import subprocess
import os
import re
from pathlib import Path
# cmd : dune exec frequify -- -f [freq] -o [out] [dir]

in_dir_str = "./underapproximation_type/data/validation/"
out_dir_str = "../Cobb_PBT/bin/"

folder_names = {
    "completetree":"complete_tree",
    "depth_bst":"bsts",
    "depthtree":"depth_tree",
    "duplicatelist":"duplicate_list",
    "even_list":"even_list",
    "rbtree":"red_black_tree",
    "sizedlist":"sized_list",
    "sortedlist":"sorted_list",
    "uniquelist":"unique_list",
}

t_pattern = r"true"
f_pattern = r"false"

in_dir = Path(in_dir_str)
assert in_dir.is_dir()

# prog*.ml
for d in (os.listdir(in_dir)):
    gen_d = f"{in_dir}/{d}"
    match = re.search(r"(?:_excess)|(?:_imprecise)|(?:_[123]){1}|(?:_size)|(?:proofs)$", d)

    if (os.path.isdir(gen_d) and not match):
        is_stlc = re.search(r"stlc", d)
        if not (is_stlc):
            for f in os.listdir(gen_d):
                match = re.search(r"^prog[0-9]+\.ml.syn$", f)
                if match: 
                    in_file = f"{gen_d}/{f}"
                    base, ext, nothing = f.partition(".ml")
                    if d in folder_names:
                        out_file = f"{out_dir_str}{folder_names[d]}/{base}_syn{ext}"
                    else:
                        out_file = f"{out_dir_str}{d}/{base}_syn{ext}"

                    try:
                        with open(in_file, "r") as fin:
                            lines = fin.readlines()

                        with open(in_file, "w") as fout:
                            for line in lines:
                                new_line = re.sub(t_pattern, "True", line) 
                                new_line = re.sub(f_pattern, "False", new_line) 
                                fout.write(new_line)
                    
                    except FileNotFoundError:
                        print(f"Error: The file '{file}' was not found.")
                    
                    if d == "rbtree":
                        cmd = f"dune exec frequify -- -f unif_gen -o {out_file} {in_file}".split(" ")
                    else:
                        cmd = f"dune exec frequify -- -f freq_gen -o {out_file} {in_file}".split(" ")
                    subprocess.run(cmd)

                    try:
                        with open(in_file, "w") as fout:
                            for line in lines:
                                fout.write(line)
                    
                    except FileNotFoundError:
                        print(f"Error: The file '{file}' was not found.")
            
