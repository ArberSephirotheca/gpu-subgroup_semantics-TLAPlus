#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
from pathlib import Path
import re

import amber_test_generation
from configuration import Configuration


GROUP_TO_PREFIX = {
    "2_threads_2_instructions": "2t_2i",
    "2_threads_3_instructions": "2t_3i",
    "2_threads_4_instructions": "2t_4i",
    "3_threads_3_instructions": "3t_3i",
    "3_threads_4_instructions": "3t_4i",
}

SATURATION_TO_SUFFIX = {
    3: "waterfall_queue",
    4: "global_barrier",
}


def _build_input_path(all_tests_flat: Path, group_name: str, test_id: str) -> Path:
    if group_name not in GROUP_TO_PREFIX:
        raise ValueError(f"Unsupported suite directory: {group_name}")
    prefix = GROUP_TO_PREFIX[group_name]
    return all_tests_flat / f"{prefix}_{test_id}" / f"{test_id}.txt"


TEMPLATE_RE = re.compile(r"^(?P<test_id>\d+)_txt_(?P<variant>.+)\.amber$")


def _discover_templates(source_root: Path) -> list[Path]:
    return sorted(source_root.rglob("*_txt_*.amber"))


def _mk_config(saturation_level: int) -> Configuration:
    return Configuration(
        timeout=10000,
        workgroups=65532,
        threads_per_workgroup=128,
        saturation_level=saturation_level,
        subgroup=0,
        subgroup_size=32,
    )


def _parse_template_name(template: Path) -> tuple[str, str]:
    match = TEMPLATE_RE.match(template.name)
    if not match:
        raise ValueError(f"Unsupported template filename format: {template}")
    return match.group("test_id"), match.group("variant")


def _generate_variant(
    source_template: Path,
    out_root: Path,
    all_tests_flat: Path,
    saturation_level: int,
    cfg: Configuration,
) -> None:
    suffix = SATURATION_TO_SUFFIX[saturation_level]
    group_name = source_template.parent.name
    test_id, source_variant = _parse_template_name(source_template)

    input_txt = _build_input_path(all_tests_flat, group_name, test_id)
    if not input_txt.is_file():
        raise FileNotFoundError(f"Missing source txt: {input_txt}")

    output_dir = out_root / group_name
    output_dir.mkdir(parents=True, exist_ok=True)
    output_base = output_dir / f"{test_id}_txt_{source_variant}_{suffix}"

    amber_test_generation.generate_amber_test(str(input_txt), str(output_base), cfg)


def main() -> int:
    dynamic_wg_dir = Path(__file__).resolve().parents[1]
    template_root = dynamic_wg_dir / "test_amber" / "template_test_suite"

    parser = argparse.ArgumentParser(
        description=(
            "Generate weak_fair barrier variants from all weak_fair templates.\n"
            "Produces two suites: waterfall_queue and global_barrier."
        )
    )
    parser.add_argument(
        "--source",
        type=Path,
        default=template_root / "weak_fair",
        help="Source weak_fair suite root (default: template_test_suite/weak_fair).",
    )
    parser.add_argument(
        "--out-waterfall",
        type=Path,
        default=template_root / "weak_fair_waterfall_queue",
        help="Output root for waterfall_queue templates.",
    )
    parser.add_argument(
        "--out-global-barrier",
        type=Path,
        default=template_root / "weak_fair_global_barrier",
        help="Output root for global_barrier templates.",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Delete output roots before generation.",
    )
    args = parser.parse_args()

    source_root = args.source.resolve()
    out_waterfall = args.out_waterfall.resolve()
    out_global = args.out_global_barrier.resolve()
    all_tests_flat = (dynamic_wg_dir / "ALL_tests_flat").resolve()

    if not source_root.is_dir():
        raise FileNotFoundError(f"Source root not found: {source_root}")
    if not all_tests_flat.is_dir():
        raise FileNotFoundError(f"ALL_tests_flat root not found: {all_tests_flat}")

    templates = _discover_templates(source_root)
    if not templates:
        raise RuntimeError(f"No templates found under: {source_root}")

    if args.clean:
        for path in [out_waterfall, out_global]:
            if path.exists():
                shutil.rmtree(path)

    waterfall_cfg = _mk_config(3)
    global_cfg = _mk_config(4)

    for template in templates:
        _generate_variant(template, out_waterfall, all_tests_flat, 3, waterfall_cfg)
        _generate_variant(template, out_global, all_tests_flat, 4, global_cfg)

    print(f"Generated {len(templates)} waterfall_queue templates in: {out_waterfall}")
    print(f"Generated {len(templates)} global_barrier templates in: {out_global}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
