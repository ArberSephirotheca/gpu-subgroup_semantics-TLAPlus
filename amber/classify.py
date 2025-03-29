import os
import re
import shutil
import glob
import csv

try:
    from tabulate import tabulate
    USE_TABULATE = True
except ImportError:
    USE_TABULATE = False

cadp_root = 'cadp'
amber_root_base = 'empirical_testing/test_amber'

# Track copied files per GPU and variant
copied_files = {}  # { gpu_dir: { 'weak_HSA': {cadp_subdir: set(test_ids)}, 'weak_OBE': {...} } }

for cadp_subdir in os.listdir(cadp_root):
    cadp_subdir_path = os.path.join(cadp_root, cadp_subdir)
    if not os.path.isdir(cadp_subdir_path):
        continue

    alloy_path = os.path.join(cadp_subdir_path, 'alloy_output_processed')
    if not os.path.exists(alloy_path):
        continue

    for subdir in os.listdir(alloy_path):
        subdir_path = os.path.join(alloy_path, subdir)
        label_file = os.path.join(subdir_path, f'label_{subdir}.txt')
        if not os.path.isfile(label_file):
            continue

        with open(label_file, 'r') as f:
            content = f.read()

        hsa_pass = re.search(r'HSA - Termination: PASS', content)
        obe_pass = re.search(r'OBE - Termination: PASS', content)

        if not (hsa_pass or obe_pass):
            continue

        gpu_dirs = glob.glob(os.path.join(amber_root_base, '*'))

        for gpu_dir in gpu_dirs:
            amber_test_dir = os.path.join(gpu_dir, cadp_subdir)
            if not os.path.exists(amber_test_dir):
                continue

            # Track test IDs per variant
            copied_files.setdefault(gpu_dir, {'weak_HSA': {}, 'weak_OBE': {}})
            if hsa_pass:
                copied_files[gpu_dir]['weak_HSA'].setdefault(cadp_subdir, set())
            if obe_pass:
                copied_files[gpu_dir]['weak_OBE'].setdefault(cadp_subdir, set())

            for amber_file in os.listdir(amber_test_dir):
                if amber_file.startswith(f'{subdir}_txt') and amber_file.endswith('.amber'):
                    amber_file_path = os.path.join(amber_test_dir, amber_file)
                    test_id_match = re.match(r'(\d+)_txt', amber_file)
                    if not test_id_match:
                        continue
                    test_id = test_id_match.group(1)

                    if hsa_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_HSA', cadp_subdir)
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)
                        copied_files[gpu_dir]['weak_HSA'][cadp_subdir].add(test_id)

                    if obe_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_OBE', cadp_subdir)
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)
                        copied_files[gpu_dir]['weak_OBE'][cadp_subdir].add(test_id)

# Filter, rewrite CSVs, and produce final ASCII tables (written to file, not printed)
for gpu_dir, variants in copied_files.items():
    for variant_name in ['weak_HSA', 'weak_OBE']:
        for cadp_subdir, test_ids in variants[variant_name].items():
            amber_test_dir = os.path.join(gpu_dir, cadp_subdir)
            csv_files = glob.glob(os.path.join(amber_test_dir, 'simple_final_results-*.csv'))
            if not csv_files:
                continue

            csv_file = csv_files[0]  # Use the first found
            # Read CSV
            with open(csv_file, newline='') as f:
                reader = list(csv.reader(f))
            if not reader:
                continue

            header = reader[0]
            rows = reader[1:]

            # Filtered rows
            filtered_rows = [header]
            for row in rows:
                if not row:
                    continue
                # row[0] is the test_id presumably
                if row[0].isdigit() and row[0] in test_ids:
                    filtered_rows.append(row)
                elif row[0].startswith("Total failures"):
                    break  # skip old summary lines

            # Write filtered CSV next to copied .amber files
            variant_dir = os.path.join(gpu_dir, variant_name, cadp_subdir)
            if not filtered_rows or len(filtered_rows) == 1:
                continue  # no actual test rows

            output_csv_path = os.path.join(variant_dir, os.path.basename(csv_file))
            with open(output_csv_path, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerows(filtered_rows)

            # Now produce the final summary row & ASCII table:
            # We assume columns 1..N are "P"/"F" fields, ignoring column 0 (TestID).
            table = [filtered_rows[0]]  # first row is header
            data_only = filtered_rows[1:]  # the actual test data

            num_cols = len(table[0]) - 1
            fail_counts = [0] * num_cols

            for row in data_only:
                for i in range(num_cols):
                    # row[i+1] is presumably "P" or "F"
                    if len(row) > i+1 and row[i+1].strip() == 'F':
                        fail_counts[i] += 1

            total_failures_row = ["Total failures:"]
            for fc in fail_counts:
                total_failures_row.append(str(fc))

            table.extend(data_only)
            table.append(total_failures_row)

            # Write the fancy table to a file (rather than printing).
            table_txt_path = os.path.join(variant_dir, "final_summary_table.txt")
            if USE_TABULATE:
                table_str = tabulate(table, headers='firstrow', tablefmt='fancy_grid')
            else:
                # Fallback: simple lines
                lines = []
                lines.append(" | ".join(table[0]))  # header
                for r in data_only:
                    lines.append(" | ".join(r))
                lines.append(" | ".join(total_failures_row))
                table_str = "\n".join(lines)

            with open(table_txt_path, 'w', encoding='utf-8') as out_f:
                out_f.write(table_str)

print("✅ Done! Copied .amber files, filtered CSVs, and wrote final ASCII tables to 'final_summary_table.txt'.")
