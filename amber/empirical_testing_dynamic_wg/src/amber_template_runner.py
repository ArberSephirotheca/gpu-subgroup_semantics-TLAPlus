#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
import sys
import tempfile


PLACEHOLDER_NUM_WORKGROUPS = "NUMWORKGROUPS"
PLACEHOLDER_TOTAL_THREADS = "TOTALTHREADS"


def _parse_threads_per_workgroup(amber_text: str) -> int:
    match = re.search(r"layout\s*\(\s*local_size_x\s*=\s*(\d+)\s*,", amber_text)
    if not match:
        raise ValueError("Could not find 'layout(local_size_x = N, ...)' in template.")
    return int(match.group(1))


def _instantiate_template(amber_text: str, workgroups: int) -> tuple[str, int, int]:
    if PLACEHOLDER_NUM_WORKGROUPS not in amber_text:
        raise ValueError(f"Template is missing placeholder '{PLACEHOLDER_NUM_WORKGROUPS}'.")
    if PLACEHOLDER_TOTAL_THREADS not in amber_text:
        raise ValueError(f"Template is missing placeholder '{PLACEHOLDER_TOTAL_THREADS}'.")

    threads_per_workgroup = _parse_threads_per_workgroup(amber_text)
    total_threads = workgroups * threads_per_workgroup

    instantiated = (
        amber_text.replace(PLACEHOLDER_NUM_WORKGROUPS, str(workgroups)).replace(
            PLACEHOLDER_TOTAL_THREADS, str(total_threads)
        )
    )
    return instantiated, threads_per_workgroup, total_threads


def _split_script_and_amber_args(argv: list[str]) -> tuple[list[str], list[str]]:
    try:
        split_index = argv.index("--")
    except ValueError:
        return argv, []
    return argv[:split_index], argv[split_index + 1 :]


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Instantiate an Amber template by replacing NUMWORKGROUPS and TOTALTHREADS, then run amber.\n"
            "Pass amber flags after '--', e.g.:\n"
            "  amber_template_runner.py template.amber --workgroups 64 -- -d -t spv1.5"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "template",
        help="Path to a .amber template containing placeholders NUMWORKGROUPS and TOTALTHREADS.",
    )
    parser.add_argument(
        "--workgroups",
        type=int,
        required=True,
        help="Number of workgroups to substitute for NUMWORKGROUPS.",
    )
    parser.add_argument(
        "--amber",
        default="amber",
        help="Path to the amber executable (default: amber).",
    )
    parser.add_argument(
        "--keep-temp",
        action="store_true",
        help="Keep the instantiated temporary .amber file (prints its path).",
    )

    script_argv, amber_argv = _split_script_and_amber_args(sys.argv[1:])
    args = parser.parse_args(script_argv)

    if args.workgroups <= 0:
        parser.error("--workgroups must be a positive integer.")

    try:
        with open(args.template, "r", encoding="utf-8") as file:
            template_text = file.read()
    except OSError as e:
        print(f"Failed to read template: {e}", file=sys.stderr)
        return 2

    try:
        instantiated_text, threads_per_workgroup, total_threads = _instantiate_template(
            template_text, args.workgroups
        )
    except ValueError as e:
        print(str(e), file=sys.stderr)
        return 2

    temp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".amber",
            prefix="amber_instantiated_",
            delete=False,
        ) as temp_file:
            temp_file.write(instantiated_text)
            temp_path = temp_file.name

        cmd = [args.amber]
        if amber_argv:
            cmd.extend(amber_argv)
        cmd.append(temp_path)

        if args.keep_temp:
            print(
                f"Using temp file: {temp_path} (workgroups={args.workgroups}, "
                f"threads_per_workgroup={threads_per_workgroup}, total_threads={total_threads})"
            )

        completed = subprocess.run(cmd, check=False)
        return completed.returncode
    finally:
        if temp_path and not args.keep_temp:
            try:
                os.remove(temp_path)
            except OSError:
                pass


if __name__ == "__main__":
    raise SystemExit(main())
