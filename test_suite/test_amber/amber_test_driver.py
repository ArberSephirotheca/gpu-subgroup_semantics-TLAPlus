#!/usr/bin/env python3
# -----------------------------------------------------------------------
# amber_test_driver.py
# Authors: Hari Raval and Tyler Sorensen
# -----------------------------------------------------------------------
import argparse
import os
import sys
sys.path.insert(0,"../src/")
import re
import csv
import socket  # to get hostname
import subprocess
from configuration import Configuration
import amber_test_generation
from tabulate import tabulate
from datetime import date
from datetime import datetime
import time

AMBER_PATHS = ["amber"]

LOG_FILE = None


# define a log print function
def log_print(s):
    global LOG_FILE
    LOG_FILE.write(s + "\n")
    print(s)


# create amber tests with provided input directory and specified configuration object and path/build details
def run_amber_test(input_dir, output_dir, each_cfg_option, amber_build_path, amber_build_flags, num_iter, android):
    simple_test_results = []
    verbose_test_results = []
    all_test_results = []

    # iterate over all files in the input directory, create a .amber file for each .comp file, and run the amber file
    for file_name in os.listdir(input_dir):
        if file_name.endswith('.comp'):
            # input file name shouldn't end with .amber as the amber_test_generation.py script will add the extension
            output_file_name = file_name[:-5]
            input_file_name = os.path.join(input_dir, file_name)
            log_print("generating amber test for: " + file_name + " in " + output_dir)
            # create the amber file associated with input_file_name
            amber_test_generation.generate_amber_test(input_file_name, output_file_name, each_cfg_option)

            output_file_name = output_file_name + ".amber"

            # generate command to run the amber test for a specified iteration count and append results to a temp file
            run__test = "timeout -k 1 15 " + amber_build_path + output_file_name + amber_build_flags + ">> temp_results.txt"
            if android:
                # push test file on the device
                os.system("adb push " + output_file_name + " /data/local/tmp/")
                # prepare the specific run command to run amber on-device
                run__test = "timeout -k 1 15 adb shell 'cd /data/local/tmp ; ./amber_ndk " + amber_build_flags + " " + os.path.basename(
                    output_file_name) + "' >> temp_results.txt"
            for i in range(int(num_iter)):
                log_print("running test: " + output_file_name)
                log_print(run__test)
                os.system(run__test)

            # analyze the results of the temporary file to determine whether the test passed (P) or failed (F)
            with open('temp_results.txt', 'r') as file:
                results = file.read().split("\n")
                test_iteration = file_name[:-5]
                failure_count = 0
                pass_count = 0

                # count the number of failures, if any, and update both simple and verbose results accordingly
                for current_line in results:
                    if "1 fail" in current_line:
                        failure_count = failure_count + 1
                    elif "1 pass" in current_line:
                        pass_count = pass_count + 1

                # if there were no failures, indicate a "P" in both sets of tables
                if failure_count == 0:
                    log_print("P")
                    temp_item = [test_iteration, "P"]
                    simple_test_results.append(temp_item)
                    verbose_test_results.append(temp_item)

                # if there is at least one failure, update simple table with "F" and verbose table with fraction of "F"
                else:
                    log_print("F")
                    fract = "F (" + str(failure_count) + "/" + str(num_iter) + ")"
                    temp_item_verbose = [test_iteration, fract]
                    temp_item_simple = [test_iteration, "F"]
                    simple_test_results.append(temp_item_simple)
                    verbose_test_results.append(temp_item_verbose)

            os.system("rm -f temp_results.txt")
            # create a directory of the amber test scripts generated at the specified output directory
            log_print("")
            move_amber_test_file = "mv " + output_file_name + " " + output_dir
            os.system(move_amber_test_file)

    os.system("rm -f temp_results.txt")
    all_test_results.append(simple_test_results)
    all_test_results.append(verbose_test_results)

    return all_test_results


# main driver function to create amber files with the specified list of configuration objects, provided
# input directory, and details of the build path/type
def amber_driver(all_config_variants, input_dir, output_dir, amber_build_path, amber_build_flags, num_iter, android):
    simple_results = []
    verbose_results = []

    for each_cfg_opt in all_config_variants:
        temp_results = run_amber_test(input_dir, output_dir, each_cfg_opt, amber_build_path, amber_build_flags,
                                      num_iter, android)
        if len(temp_results) != 2:
            print("An error occurred during the generation of the amber tests in run_amber_test()", file=sys.stderr)
            exit(1)
        simple_results.append(temp_results[0])
        verbose_results.append(temp_results[1])

    default_config_length = len(simple_results[0])
    for (result1, result2) in zip(simple_results, verbose_results):
        if len(result1) != default_config_length or len(result2) != default_config_length:
            print("The number of results from each of the configuration settings must be the same", file=sys.stderr)
            exit(1)

    final_simple_results = []
    final_verbose_results = []

    running_failure_sum_simple = [0] * (len(all_config_variants) + 1)
    running_failure_sum_simple[0] = "Total failures:"
    running_failure_sum_verbose = [0] * (len(all_config_variants) + 1)
    running_failure_sum_verbose[0] = "Total failures:"

    for index, (simple_list, verbose_list) in enumerate(zip(simple_results, verbose_results)):
        counter_simple = sum(1 for r in simple_list if r[1] == "F")
        counter_verbose = sum(1 for r in verbose_list if "F" in r[1])
        running_failure_sum_simple[index + 1] = counter_simple
        running_failure_sum_verbose[index + 1] = counter_verbose

    any_passed_sum_simple = 0
    any_passed_sum_verbose = 0

    # 🔄 Changed: test IDs as strings
    test_ids = [test[0] for test in simple_results[0]]

    # 🔄 Sort: "reference" first, then the rest numerically if possible
    def sort_key(x):
        if x == "reference":
            return (-1,)
        try:
            return (int(x),)
        except ValueError:
            return (float("inf"), x)

    test_ids.sort(key=sort_key)

    for test_id in test_ids:
        current_simple_list = [test_id]
        current_verbose_list = [test_id]

        for each_simple_config_result, each_verbose_config_result in zip(simple_results, verbose_results):
            s_match = next((r for r in each_simple_config_result if r[0] == test_id), ["?", "M"])
            v_match = next((r for r in each_verbose_config_result if r[0] == test_id), ["?", "M"])
            current_simple_list.append(s_match[1])
            current_verbose_list.append(v_match[1])

        current_simple_list.append("F" if "F" in current_simple_list else "P")
        current_verbose_list.append("F" if any("F" in r for r in current_verbose_list[1:]) else "P")

        final_simple_results.append(current_simple_list)
        final_verbose_results.append(current_verbose_list)

        if current_simple_list[-1] == "F":
            any_passed_sum_simple += 1
        if "F" in str(current_verbose_list[-1]):
            any_passed_sum_verbose += 1

    running_failure_sum_simple.append(any_passed_sum_simple)
    running_failure_sum_verbose.append(any_passed_sum_verbose)
    final_simple_results.append(running_failure_sum_simple)
    final_verbose_results.append(running_failure_sum_verbose)

    log_print("")
    log_print("Finished running tests!")
    log_print("")

    format_output_results(final_simple_results, final_verbose_results, all_config_variants, output_dir)


# prepare the headers and file name information for each type of file outputted
def format_output_results(final_simple_results, final_verbose_results, all_config_variants, output_dir):
    today = date.today()
    td = today.strftime("%Y-%m-%d")
    # create a list of headers for the output files based off of the configuration types used
    headers = ["Test File Name"]
    headers.append("All Passed")

    format_ascii_table_output(final_simple_results, final_verbose_results, output_dir, headers, td)
    format_csv_table_output(final_simple_results, final_verbose_results, output_dir, headers, td)
    format_html_table_output(final_simple_results, output_dir, headers, td)


# output both the iterative and non-iterative results into ascii tables
def format_ascii_table_output(final_simple_results, final_verbose_results, output_dir, headers, td):
    output_name_simple_txt = output_dir + "/" + "simple_final_results-" + td + ".txt"
    output_name_verbose_txt = output_dir + "/" + "iteration_based_final_results-" + td + ".txt"

    # open and write results to the simple .txt file
    output_file_txt = open(output_name_simple_txt, "w+")
    log_print("writing simple ascii table to:")
    log_print(output_name_simple_txt)
    log_print("")
    output_file_txt.write(tabulate(final_simple_results, headers=headers, tablefmt="fancy_grid"))
    output_file_txt.write("\n")
    output_file_txt.close()

    # open and write results to the verbose .txt file
    output_file_txt = open(output_name_verbose_txt, "w+")
    log_print("writing iteration-based ascii table to:")
    log_print(output_name_verbose_txt)
    log_print("")
    output_file_txt.write(tabulate(final_verbose_results, headers=headers, tablefmt="fancy_grid"))
    output_file_txt.write("\n")
    output_file_txt.close()


# output both the iterative and non-iterative results into csv tables
def format_csv_table_output(final_simple_results, final_verbose_results, output_dir, headers, td):
    output_name_simple_csv = output_dir + "/" + "simple_final_results-" + td + ".csv"
    output_name_verbose_csv = output_dir + "/" + "iteration_based_final_results-" + td + ".csv"

    log_print("writing simple csv table to:")
    log_print(output_name_simple_csv)
    log_print("")

    # open and write simple results to a .csv file
    with open(output_name_simple_csv, "w") as csv_file:
        writer = csv.writer(csv_file, delimiter=',')

        writer.writerow(headers)

        for line in final_simple_results:
            writer.writerow(line)
    csv_file.close()

    log_print("writing simple csv table to:")
    log_print(output_name_simple_csv)
    log_print("")

    # open and write verbose results to a .csv file
    with open(output_name_verbose_csv, "w") as csv_file:
        writer = csv.writer(csv_file, delimiter=',')
        writer.writerow(headers)
        for line in final_verbose_results:
            writer.writerow(line)
    csv_file.close()


# output the non-iterative results into a formatted html table
def format_html_table_output(final_simple_results, output_dir, headers, td):
    output_name_html = output_dir + "/" + "html-colored-table" + td + ".html"

    # open and write results to the html .txt file
    output_file_txt = open(output_name_html, "w+")
    log_print("writing colored html table to:")
    log_print(output_name_html)
    log_print("")
    html = tabulate(final_simple_results, headers, tablefmt="html").split("\n")

    # extract the rows that contain pass/fail data
    data_rows = []
    for each_line in html:
        if "<tr><td>" in each_line:
            data_rows.append(each_line)

    colored_data_rows = []

    # color each cell of data according to the result status (pass = green, fail = red)
    for row, curr_line in enumerate(data_rows):
        curr_line_list = curr_line.split(" ")
        while "" in curr_line_list:
            curr_line_list.remove("")

        if row < (len(data_rows) - 1):
            href = "https://www.cs.princeton.edu/~ls24/testExplorer.html?threads=" + input_test_type[0] + "&instructions=" + input_test_type[1] + "&test=" + str(row)
            curr_line_list[0] = '<tr><td><a href="' + href + '">' + str(row) + '</a>'

        for index, item in enumerate(curr_line_list):
            if "P" in item:
                curr_line_list[index] = '<td bgcolor="#009900">P'
            if "F" in item:
                curr_line_list[index] = '<td bgcolor="#CC0000">F'

        colored_data_rows.append(curr_line_list)

    # merge the data back into proper html string format
    merged_data = [' '.join(row) for row in colored_data_rows]
    updated_data_as_str = "\n".join(merged_data)

    # create the string of html code to be written to the output file
    begin_html = html[:5]
    beg_str = "\n".join(begin_html)
    end_html = html[-2:]
    end_str = "\n".join(end_html)
    html_table = beg_str + updated_data_as_str + end_str

    # boiler plate code for html_table (Cite: https://www.w3schools.com/tags/tryit.asp?filename=tryhtml_td_bgcolor)

    start_boiler_plate = "<!DOCTYPE html> \n<html> \n<head> \n<style> \ntable, th, td {" \
                         "\n  border: 1px solid black; \n} \n</style> \n</head> \n<body> \n" \
                         "<h1>Colored Amber Test Results</h1>\n"

    end_boiler_plate = "\n</body> \n</html> \n"

    output_file_txt.write(start_boiler_plate + html_table + end_boiler_plate)
    output_file_txt.write("\n")
    output_file_txt.close()


# automatically find the amber build path
def find_amber():
    for a in AMBER_PATHS:
        cmd = "which " + a + " > /dev/null"
        ret = os.system(cmd)
        if ret == 0:
            log_print("found amber executable: ")
            log_print(a)
            log_print("")
            return a
    log_print("unable to find an amber executable")
    assert (0)


# create a directory to hold the output
def get_new_dir_name():
    base_name = "results/output"
    label = 0
    while 1:
        check_name = base_name + str(label)
        if not os.path.exists(check_name):
            print("writing results to:")
            print(check_name)
            print("")
            return check_name
        label += 1


def android_sanity_check():
    """Check that Android device is accessible, and amber is installed as /data/local/tmp/amber_ndk"""
    try:
        subprocess.run(["adb", "shell", "true"], timeout=5, check=True)
    except:
        print("Error: no Android device connected?")
        exit(1)

    try:
        subprocess.run(["adb", "shell", "test -f /data/local/tmp/amber_ndk"], timeout=5, check=True)
    except:
        print(
            "Error: on Android device, /data/local/tmp/amber_ndk was not found. Please install Amber at this precise location.")
        exit(1)


def main():
    global LOG_FILE

    parser = argparse.ArgumentParser()
    parser.add_argument('input_dir', help='Path to input directory containing test in text format')
    parser.add_argument('num_iterations', type=int, help='Number of iteration to run each test')
    parser.add_argument('--android', action='store_true',
                        help='Run on Android device. Assumes a single Android device is connected, accessible with adb, and with amber already installed as /data/local/tmp/amber_ndk')
    args = parser.parse_args()

    if args.android:
        android_sanity_check()

    start = time.time()

    input_dir = args.input_dir

    global input_test_type
    input_test_type = re.findall(r'\d+', str(input_dir))
    if len(input_test_type) != 2:
        input_test_type = ['X', 'X']

    num_iterations = args.num_iterations

    # the user must input the location of the directory where the .amber files will reside
    output_dir_path = get_new_dir_name()

    # the user may change the flags used to build the amber tests with (include spaces before and after the flag(s))
    amber_build_flags = " -d -t spv1.5 "

    os.makedirs(output_dir_path, exist_ok=True)

    log_file_name = output_dir_path + "/output_log.txt"
    LOG_FILE = open(log_file_name, 'w')
    log_print("Date and Time:")
    now = datetime.now()
    nowpp = now.strftime("%d/%m/%Y %H:%M:%S")
    log_print(nowpp)
    log_print("Computer:")
    log_print(socket.gethostname())
    log_print("")

    # Store Vulkan info
    vulkan_info = output_dir_path + "/vulkaninfo.txt"
    if args.android:
        log_print("No vulkaninfo on Android")
    else:
        log_print("storing vulkaninfo to: " + vulkan_info)
        log_print("")
        os.system("vulkaninfo > " + vulkan_info)

    if args.android:
        amber_build_path = ""  # ignored anyway
    else:
        amber_build_path =  "amber "

    # the user must provide all the possible configuration objects they want to test with, placing them in the
    # all_config_variants list below
    default_cfg = Configuration(timeout=10000, workgroups=65532, threads_per_workgroup=128, saturation_level=0, subgroup=0, subgroup_size=32)
    # round_r_cfg = Configuration(timeout=10000, workgroups=65532, threads_per_workgroup=128, saturation_level=1, subgroup=0, subgroup_size=32)
    # chunk_cfg = Configuration(timeout=10000, workgroups=65532, threads_per_workgroup=128, saturation_level=2, subgroup=0, subgroup_size=32)

    all_config_variants = [default_cfg]

    # call the main driver function
    amber_driver(all_config_variants, input_dir, output_dir_path, amber_build_path, amber_build_flags, num_iterations,
                 args.android)
    end = time.time()
    log_print("")
    log_print("Execution time (s):")
    log_print(str(end - start))
    LOG_FILE.close()


if __name__ == "__main__":
    main()
