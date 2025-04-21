# -----------------------------------------------------------------------
# amber_launch_tests.py
# Authors: Hari Raval
# -----------------------------------------------------------------------
import sys
import os
import argparse


# run the amber_test_driver.py script with all input directories available in Input_Files
def main():

    parser = argparse.ArgumentParser()
    parser.add_argument('--android', action='store_true', help='Android tests')
    parser.add_argument('--serial', help='serial number of device (if more than one attached with adb)')
    parser.add_argument('--device', help='vulkan device id (if more than 1 vulkan device available)')

    args = parser.parse_args()

    directory_names = ["../ALL_tests_tmp/2_thread_2_instruction",
                       "../ALL_tests_tmp/2_thread_3_instruction",
                       "../ALL_tests_tmp/2_thread_4_instruction",
                       "../ALL_tests_tmp/3_thread_3_instruction",
                       "../ALL_tests_tmp/3_thread_4_instruction"]

    for name in directory_names:
        command = "python3 amber_test_driver.py " + name + " 1"
        if args.android:
            command += " --android"
        if args.serial:
            command += f" --serial {args.serial}"
        if args.device:
            command += f" --device {args.device}"
        os.system(command)


if __name__ == "__main__":
    main()
