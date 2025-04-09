#
# amber_test_generation.py
# Author: Hari Raval #

import sys
import re
from configuration import Configuration

# Configuration object to be used in the Amber test generation

# Notes: saturation_level describes the heuristic of running many
# instances of the same test in the same kernel. Each instance of the
# test operate on distinct memory. There are 3 options for saturation
# that dictate how threads are mapped to test instances. NOTE THAT
# SATURATION IS NOT CURRENTLY CURRENTLY SUPPORTED FOR INTRA-WORKGROUP
# AND INTRA-SUBGROUP TESTS:
# The saturation_level can be set to:

# 0 - no saturation

# 1 - Round Robin: threads are assigned to test instances in a round robin fasion

# 2 - Chunking: threads are assigned to test instances in a course
# grained chunk (first N threads are assigned to testing thread 0,
# second N threads are assigned to testing thread 1, etc.

# Workgroups is the max supported number across a variety of GPUs
# (65532). Timeout is how many milliseconds to wait until killing the
# kernel (20 seconds). threads_per_workgroup is set to 1 so that each
# test goes across workgroups. Increasing this will allow
# intra-workgroup behavior to be tested, but can mess up saturation
# hueristics. subgroup will include the GLSL subgroup extension and
# ensure that testing threads are in different subgroups.
default_config = Configuration(timeout=10000, workgroups=65532, threads_per_workgroup=32, saturation_level=0, subgroup=0, subgroup_size=32)


# write the necessary "boiler plate" code to generate an Amber test, along with Shader
# Storage Buffer Object(s), workgroup size, and global variable to
# assign thread IDs. output is the file being written to, timeout determines (in ms) when the
# program will terminate, num_testing_subgroups is the number of threads being tested, and saturation_level is the
# type of saturation (if any)
def write_amber_prologue(data, output, timeout, threads_per_workgroup, workgroups,
                         subgroup_setting, subgroup_size):
    output.write("#!amber\n")
    output.write("\n")
    output.write("SET ENGINE_DATA fence_timeout_ms " + str(timeout) + "\n")
    output.write("\n")
    output.write("SHADER compute test GLSL\n")

    # determine whether the same or different subgroups will be used for testing to update versions and extensions
    output.write(data)

    output.write("\n")

# write the necessary "boiler plate" code to end the amber test, along with generating a desired number of threads
def write_amber_epilogue(output, workgroups, threads_per_workgroup):
    total_threads = workgroups * threads_per_workgroup
    output.write("END\n")
    output.write("\n")

    # output.write("BUFFER pickthread DATA_TYPE uint32 SIZE 1 FILL 0\n")
    # fill the tester SSBO with 1 or 2 zeroes depending on the saturation level
    output.write("BUFFER tester DATA_TYPE uint32 SIZE " + str(total_threads) + " FILL 0\n")
    output.write("BUFFER expected DATA_TYPE uint32 SIZE " + str(total_threads) + " FILL 2\n")
    output.write("BUFFER injection DATA_TYPE vec2<float> DATA\n 0.0 1.0\nEND\n")

    output.write("\n")
    output.write("PIPELINE compute test_pipe\n")
    output.write("  ATTACH test\n")
    # output.write("  BIND BUFFER pickthread AS storage DESCRIPTOR_SET 0 BINDING 3 \n")
    output.write("  BIND BUFFER tester AS storage DESCRIPTOR_SET 0 BINDING 0 \n")
    output.write("  BIND BUFFER injection AS uniform DESCRIPTOR_SET 0 BINDING 1 \n")


    output.write("\n")
    output.write("END\n")
    output.write("\n")
    output.write("RUN test_pipe " + str(workgroups) + " 1 1\n")

    output.write("EXPECT tester EQ_BUFFER expected\n")


# generate an Amber test with a provided input file, a desired output file name, and a Configuration object to set up
# the number of workgroups, threads per workgroup, and timeout
def generate_amber_test(inputted_file, output_file_name, config=default_config):
    input_file = inputted_file
    timeout = config.get_timeout()
    subgroup_set = int(config.get_subgroup_setting())
    subgroup_size = int(config.get_subgroup_size())

    if output_file_name.endswith(".amber"):
        print("Script will include the .amber extension, please provide a different output file name", file=sys.stderr)
        exit(1)


    with open(input_file, 'r') as file:
        data = file.read()





    threads_per_workgroup = int(config.get_threads_per_workgroup())
    workgroups = int(config.get_number_of_workgroups())

    total_number_threads = threads_per_workgroup * workgroups

    # name and open the output file to contain the amber test case
    output_amber_file = output_file_name
    output_amber_file = output_amber_file + ".amber"
    output = open(output_amber_file, "w")

    # call the appropriate functions to generate the amber test
    write_amber_prologue(data, output, timeout, threads_per_workgroup, workgroups,
                         subgroup_set, subgroup_size)


    write_amber_epilogue(output, workgroups, threads_per_workgroup)


def main():
    if len(sys.argv) != 3:
        print("Please provide a .txt file to parse and the desired name for the outputted Amber file", file=sys.stderr)
        exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    # generate an amber test for the desired inputs, with a default configuration if none was provided
    generate_amber_test(input_file, output_file, default_config)


if __name__ == "__main__":
    main()