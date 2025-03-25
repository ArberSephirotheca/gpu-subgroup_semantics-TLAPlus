import os
import re
import shutil
import glob
import csv

# Base directories
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

# Filter and write CSVs for copied tests
for gpu_dir, variants in copied_files.items():
    for variant_name in ['weak_HSA', 'weak_OBE']:
        for cadp_subdir, test_ids in variants[variant_name].items():
            amber_test_dir = os.path.join(gpu_dir, cadp_subdir)
            csv_files = glob.glob(os.path.join(amber_test_dir, 'simple_final_results-*.csv'))
            if not csv_files:
                continue

            csv_file = csv_files[0]  # Use the first found
            with open(csv_file, newline='') as f:
                reader = list(csv.reader(f))
                header = reader[0]
                rows = reader[1:]

            filtered_rows = [header]
            for row in rows:
                if not row:
                    continue
                if row[0].isdigit() and row[0] in test_ids:
                    filtered_rows.append(row)
                elif row[0].startswith("Total failures"):
                    break  # skip summary rows

            # Write filtered CSV next to copied .amber files
            variant_dir = os.path.join(gpu_dir, variant_name, cadp_subdir)
            if filtered_rows:
                output_csv_path = os.path.join(variant_dir, os.path.basename(csv_file))
                with open(output_csv_path, 'w', newline='') as f:
                    writer = csv.writer(f)
                    writer.writerows(filtered_rows)

print("✅ Done! .amber files and filtered CSVs copied to weak_HSA / weak_OBE inside each GPU directory.")
