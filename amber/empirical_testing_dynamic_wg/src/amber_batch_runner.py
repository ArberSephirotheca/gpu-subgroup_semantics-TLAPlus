#!/usr/bin/env python3
import argparse
import csv
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


PLACEHOLDER_NUM_WORKGROUPS = "NUMWORKGROUPS"
PLACEHOLDER_TOTAL_THREADS = "TOTALTHREADS"


@dataclass(frozen=True)
class RunResult:
    template_path: Path
    workgroups: int
    returncode: int
    status: str  # PASS / FAIL / ERROR
    duration_s: float
    passes: int | None = None
    fails: int | None = None
    log_path: Path | None = None


def _split_script_and_amber_args(argv: list[str]) -> tuple[list[str], list[str]]:
    try:
        split_index = argv.index("--")
    except ValueError:
        return argv, []
    return argv[:split_index], argv[split_index + 1 :]


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


def _extract_pass_fail(output_text: str) -> tuple[int | None, int | None]:
    pass_matches = re.findall(r"\b(\d+)\s+pass\b", output_text, flags=re.IGNORECASE)
    fail_matches = re.findall(r"\b(\d+)\s+fail\b", output_text, flags=re.IGNORECASE)
    passes = int(pass_matches[-1]) if pass_matches else None
    fails = int(fail_matches[-1]) if fail_matches else None
    return passes, fails


def _default_template_paths() -> list[Path]:
    dynamic_wg_dir = Path(__file__).resolve().parents[1]
    template_root = dynamic_wg_dir / "test_amber" / "template_test_suite"
    output_style = [template_root / f"output{i}" for i in range(5)]
    if all(p.is_dir() for p in output_style):
        return output_style

    named_style = [
        template_root / "2_threads_2_instructions",
        template_root / "2_threads_3_instructions",
        template_root / "2_threads_4_instructions",
        template_root / "3_threads_3_instructions",
        template_root / "3_threads_4_instructions",
    ]
    if all(p.is_dir() for p in named_style):
        return named_style

    if template_root.is_dir():
        return sorted(
            p for p in template_root.iterdir() if p.is_dir() and not p.name.startswith("weak_")
        )
    return []


def _iter_templates(paths: Iterable[Path], recursive: bool) -> list[Path]:
    templates: set[Path] = set()
    for p in paths:
        if p.is_file():
            if p.suffix == ".amber":
                templates.add(p.resolve())
            continue
        if not p.is_dir():
            continue
        iterator = p.rglob("*.amber") if recursive else p.glob("*.amber")
        for f in iterator:
            if f.is_file():
                templates.add(f.resolve())
    return sorted(templates)


def _rel_path_under_any(path: Path, roots: list[Path]) -> Path:
    for root in roots:
        try:
            return path.relative_to(root)
        except ValueError:
            continue
    return Path(path.name)


def _sanitize_filename_component(s: str) -> str:
    # Keep it filesystem-friendly.
    return re.sub(r"[^A-Za-z0-9._-]+", "_", s)


def _run_one(
    template_path: Path,
    workgroups: int,
    amber_exe: str,
    amber_args: list[str],
    out_dir: Path | None,
    roots_for_relpath: list[Path],
    dry_run: bool,
) -> RunResult:
    start = time.time()

    template_text = template_path.read_text(encoding="utf-8", errors="replace")
    instantiated_text, _threads_per_workgroup, _total_threads = _instantiate_template(template_text, workgroups)

    rel = _rel_path_under_any(template_path, roots_for_relpath)
    log_path = None
    if out_dir is not None:
        rel_parent = rel.parent if rel.parent != Path(".") else Path()
        safe_stem = _sanitize_filename_component(rel.stem)
        log_dir = out_dir / rel_parent
        log_dir.mkdir(parents=True, exist_ok=True)
        log_path = log_dir / f"{safe_stem}__wg{workgroups}.log"

    cmd = [amber_exe, *amber_args]

    if dry_run:
        duration_s = time.time() - start
        if log_path is not None:
            log_path.write_text("DRY RUN\n" + " ".join(cmd + [str(template_path)]) + "\n", encoding="utf-8")
        return RunResult(
            template_path=template_path,
            workgroups=workgroups,
            returncode=0,
            status="DRY_RUN",
            duration_s=duration_s,
            log_path=log_path,
        )

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

        completed = subprocess.run(
            cmd + [temp_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        output = completed.stdout or ""
        passes, fails = _extract_pass_fail(output)

        # Amber can return nonzero for expectation failures; classify those as FAIL, not ERROR.
        if fails is not None and fails > 0:
            status = "FAIL"
        elif completed.returncode != 0:
            status = "ERROR"
        elif passes is not None and passes > 0 and (fails == 0 or fails is None):
            status = "PASS"
        else:
            # If Amber output format changes, fall back to return code.
            status = "PASS"

        if log_path is not None:
            log_path.write_text(output, encoding="utf-8", errors="replace")

        duration_s = time.time() - start
        return RunResult(
            template_path=template_path,
            workgroups=workgroups,
            returncode=completed.returncode,
            status=status,
            duration_s=duration_s,
            passes=passes,
            fails=fails,
            log_path=log_path,
        )
    finally:
        if temp_path is not None:
            try:
                Path(temp_path).unlink()
            except OSError:
                pass


def main() -> int:
    script_argv, amber_argv = _split_script_and_amber_args(sys.argv[1:])
    parser = argparse.ArgumentParser(
        description=(
            "Batch-run Amber template tests by instantiating NUMWORKGROUPS/TOTALTHREADS.\n"
            "Pass amber flags after '--', e.g.:\n"
            "  amber_batch_runner.py --workgroups 32 -- -v 1.2 -t spv1.5\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help=(
            "Paths to template .amber files or directories. If omitted, uses "
            "the base suites under test_amber/template_test_suite/."
        ),
    )
    parser.add_argument(
        "--workgroups",
        nargs="+",
        type=int,
        required=True,
        help="One or more workgroup counts to run each template with.",
    )
    parser.add_argument(
        "--amber",
        default="amber",
        help="Path to the amber executable (default: amber).",
    )
    parser.add_argument(
        "--no-recursive",
        action="store_true",
        help="Do not recurse into subdirectories when given a directory path.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="If set, write per-test logs and a summary CSV under this directory.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would run, but do not invoke amber.",
    )
    parser.add_argument(
        "--fail-fast",
        action="store_true",
        help="Stop after the first FAIL/ERROR.",
    )
    args = parser.parse_args(script_argv)

    if any(wg <= 0 for wg in args.workgroups):
        parser.error("--workgroups must be positive integers.")

    paths = args.paths or _default_template_paths()
    if not paths:
        parser.error("No input paths provided and no default template suite found.")

    template_files = _iter_templates(paths, recursive=not args.no_recursive)
    if not template_files:
        parser.error("No .amber files found under the provided paths.")

    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)

    # Helpful warning: default Amber target SPIR-V env is spv1.0.
    if not args.dry_run and "-t" not in amber_argv:
        print("Warning: no '-t <spv_env>' provided; Amber defaults to spv1.0.", file=sys.stderr)

    roots_for_relpath = [p.resolve() for p in paths if p.exists()]

    results: list[RunResult] = []

    total_runs = len(template_files) * len(args.workgroups)
    run_index = 0
    for template_path in template_files:
        for wg in args.workgroups:
            run_index += 1
            print(f"[{run_index}/{total_runs}] {template_path} (workgroups={wg})")
            run_start = time.time()
            try:
                result = _run_one(
                    template_path=template_path,
                    workgroups=wg,
                    amber_exe=args.amber,
                    amber_args=amber_argv,
                    out_dir=args.out_dir,
                    roots_for_relpath=roots_for_relpath,
                    dry_run=args.dry_run,
                )
            except Exception as e:
                result = RunResult(
                    template_path=template_path,
                    workgroups=wg,
                    returncode=1,
                    status="ERROR",
                    duration_s=time.time() - run_start,
                )
                print(f"ERROR: {e}", file=sys.stderr)

            results.append(result)
            if args.fail_fast and result.status in {"FAIL", "ERROR"}:
                break
        if args.fail_fast and results and results[-1].status in {"FAIL", "ERROR"}:
            break

    passed = sum(1 for r in results if r.status == "PASS")
    failed = sum(1 for r in results if r.status == "FAIL")
    errored = sum(1 for r in results if r.status == "ERROR")
    dry = sum(1 for r in results if r.status == "DRY_RUN")
    failures = failed + errored

    print("")
    print(f"Summary: PASS={passed} FAIL={failed} ERROR={errored} DRY_RUN={dry} TOTAL={len(results)}")

    if args.out_dir is not None:
        summary_path = args.out_dir / "summary.csv"
        with open(summary_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(
                [
                    "template",
                    "workgroups",
                    "status",
                    "returncode",
                    "passes",
                    "fails",
                    "duration_s",
                    "log_path",
                ]
            )
            for r in results:
                writer.writerow(
                    [
                        str(r.template_path),
                        r.workgroups,
                        r.status,
                        r.returncode,
                        "" if r.passes is None else r.passes,
                        "" if r.fails is None else r.fails,
                        f"{r.duration_s:.3f}",
                        "" if r.log_path is None else str(r.log_path),
                    ]
                )
        print(f"Wrote: {summary_path}")

    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
