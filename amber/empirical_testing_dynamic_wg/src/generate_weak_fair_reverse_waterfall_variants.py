#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path

import amber_test_generation
from configuration import Configuration


GROUP_TO_PREFIX = {
    "2_threads_2_instructions": "2t_2i",
    "2_threads_3_instructions": "2t_3i",
    "2_threads_4_instructions": "2t_4i",
    "3_threads_3_instructions": "3t_3i",
    "3_threads_4_instructions": "3t_4i",
}

SATURATION_LEVEL = 5
SUFFIX = "reverse_waterfall_queue"
TEMPLATE_RE = re.compile(r"^(?P<test_id>\d+)_txt_(?P<variant>.+)\.amber$")


def _build_input_path(all_tests_flat: Path, group_name: str, test_id: str) -> Path:
    if group_name not in GROUP_TO_PREFIX:
        raise ValueError(f"Unsupported suite directory: {group_name}")
    prefix = GROUP_TO_PREFIX[group_name]
    return all_tests_flat / f"{prefix}_{test_id}" / f"{test_id}.txt"


def _discover_templates(source_root: Path) -> list[Path]:
    return sorted(source_root.rglob("*_txt_*.amber"))


def _mk_config() -> Configuration:
    return Configuration(
        timeout=10000,
        workgroups=65532,
        threads_per_workgroup=128,
        saturation_level=SATURATION_LEVEL,
        subgroup=0,
        subgroup_size=32,
    )


def _parse_template_name(template: Path) -> tuple[str, str]:
    match = TEMPLATE_RE.match(template.name)
    if not match:
        raise ValueError(f"Unsupported template filename format: {template}")
    return match.group("test_id"), match.group("variant")


def _generate_variant(source_template: Path, out_root: Path, all_tests_flat: Path, cfg: Configuration) -> None:
    group_name = source_template.parent.name
    test_id, _source_variant = _parse_template_name(source_template)
    input_txt = _build_input_path(all_tests_flat, group_name, test_id)
    if not input_txt.is_file():
        raise FileNotFoundError(f"Missing source txt: {input_txt}")

    output_dir = out_root / group_name
    output_dir.mkdir(parents=True, exist_ok=True)
    output_base = output_dir / f"{test_id}_txt_{SUFFIX}"
    amber_test_generation.generate_amber_test(str(input_txt), str(output_base), cfg)


def main() -> int:
    dynamic_wg_dir = Path(__file__).resolve().parents[1]
    template_root = dynamic_wg_dir / "test_amber" / "template_test_suite"

    parser = argparse.ArgumentParser(
        description=(
            "Generate reverse-waterfall variants from all weak_fair templates.\n"
            "Produces one suite: reverse_waterfall_queue."
        )
    )
    parser.add_argument(
        "--source",
        type=Path,
        default=template_root / "weak_fair",
        help="Source weak_fair suite root (default: template_test_suite/weak_fair).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=template_root / "weak_fair_reverse_waterfall_queue",
        help="Output root for reverse_waterfall_queue templates.",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Delete output root before generation.",
    )
    args = parser.parse_args()

    source_root = args.source.resolve()
    out_root = args.out.resolve()
    all_tests_flat = (dynamic_wg_dir / "ALL_tests_flat").resolve()

    if not source_root.is_dir():
        raise FileNotFoundError(f"Source root not found: {source_root}")
    if not all_tests_flat.is_dir():
        raise FileNotFoundError(f"ALL_tests_flat root not found: {all_tests_flat}")

    templates = _discover_templates(source_root)
    if not templates:
        raise RuntimeError(f"No templates found under: {source_root}")

    # weak_fair includes 3 naming variants per test_id (chunking/round_robin/no_saturation)
    # but reverse-waterfall has only one queue topology, so emit one template per test_id.
    unique_templates: dict[tuple[str, str], Path] = {}
    for template in templates:
        group_name = template.parent.name
        test_id, _variant = _parse_template_name(template)
        key = (group_name, test_id)
        if key not in unique_templates:
            unique_templates[key] = template

    if args.clean and out_root.exists():
        shutil.rmtree(out_root)

    cfg = _mk_config()
    for template in sorted(unique_templates.values()):
        _generate_variant(template, out_root, all_tests_flat, cfg)

    print(
        "Generated "
        f"{len(unique_templates)} reverse_waterfall_queue templates in: {out_root} "
        f"(from {len(templates)} weak_fair source templates)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
