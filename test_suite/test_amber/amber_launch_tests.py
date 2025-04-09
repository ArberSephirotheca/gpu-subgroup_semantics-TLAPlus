# -----------------------------------------------------------------------
# amber_launch_tests.py
# Authors: Hari Raval
# -----------------------------------------------------------------------
import sys
import os


# run the amber_test_driver.py script with all input directories available in Input_Files
def main():
    if len(sys.argv) != 1:
        print("ERROR: No command line arguments required to run this higher level script")
        exit(1)

    directory_names = ["../all_tests/syn_branch_syn",
                       "../all_tests/syn_branch_syn_relax",
                       "../all_tests/syn_branch_syn_release",
                       "../all_tests/syn_lock_step",
                       "../all_tests/syn_lock_step_relax",
                       "../all_tests/syn_lock_step_release",
                       "../all_tests/syn_subgroup_op",
                       "../all_tests/syn_subgroup_op_relax",
                       "../all_tests/syn_subgroup_op_release",]

    for name in directory_names:
        os.system("python3 amber_test_driver.py " + name + " 1")


if __name__ == "__main__":
    main()
