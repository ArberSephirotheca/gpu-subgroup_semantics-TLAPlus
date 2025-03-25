import os
import re
import shutil
import glob
import csv

# Base directories
cadp_root = 'cadp'
amber_root_base = 'empirical_testing/test_amber'
output_prefix = 'output'

# Track copied files per GPU/output directory
copied_files = {}  # Structure: { gpu_dir: { 'weak_HSA': {output_num: set(filenames)}, 'weak_OBE': {...} } }

# Traverse cadp/<num''>_threads_<num'>_instructions
for cadp_subdir in os.listdir(cadp_root):
    cadp_subdir_path = os.path.join(cadp_root, cadp_subdir)
    if not os.path.isdir(cadp_subdir_path):
        continue

    match_threads = re.search(r'_threads_(\d+)_instructions', cadp_subdir)
    if not match_threads:
        continue
    output_num = match_threads.group(1)

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
            output_dir = os.path.join(gpu_dir, f'{output_prefix}{output_num}')
            if not os.path.exists(output_dir):
                continue

            # Initialize tracking
            copied_files.setdefault(gpu_dir, {'weak_HSA': {}, 'weak_OBE': {}})
            if hsa_pass:
                copied_files[gpu_dir]['weak_HSA'].setdefault(output_num, set())
            if obe_pass:
                copied_files[gpu_dir]['weak_OBE'].setdefault(output_num, set())

            for amber_file in os.listdir(output_dir):
                if amber_file.startswith(f'{subdir}_txt') and amber_file.endswith('.amber'):
                    amber_file_path = os.path.join(output_dir, amber_file)
                    test_id_match = re.match(r'(\d+)_txt', amber_file)
                    if not test_id_match:
                        continue
                    test_id = test_id_match.group(1)

                    if hsa_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_HSA', f'{output_prefix}{output_num}')
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)
                        copied_files[gpu_dir]['weak_HSA'][output_num].add(test_id)

                    if obe_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_OBE', f'{output_prefix}{output_num}')
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)
                        copied_files[gpu_dir]['weak_OBE'][output_num].add(test_id)

# After copying, filter CSVs
for gpu_dir, variants in copied_files.items():
    for variant_name in ['weak_HSA', 'weak_OBE']:
        for output_num, test_ids in variants[variant_name].items():
            output_dir = os.path.join(gpu_dir, f'{output_prefix}{output_num}')
            csv_files = glob.glob(os.path.join(output_dir, 'simple_final_results-*.csv'))
            if not csv_files:
                continue

            csv_file = csv_files[0]  # Assume only one per dir
            with open(csv_file, newline='') as f:
                reader = list(csv.reader(f))
                header = reader[0]
                rows = reader[1:]

            # Extract matching rows by test ID
            filtered_rows = [header]
            for row in rows:
                if not row or row[0].isdigit() and row[0] in test_ids:
                    filtered_rows.append(row)
                elif row[0].startswith("Total failures"):
                    break  # Skip totals

            # Write filtered csv next to copied .amber files
            variant_dir = os.path.join(gpu_dir, variant_name, f'{output_prefix}{output_num}')
            if filtered_rows:
                output_csv_path = os.path.join(variant_dir, os.path.basename(csv_file))
                with open(output_csv_path, 'w', newline='') as f:
                    writer = csv.writer(f)
                    writer.writerows(filtered_rows)

print("✅ Finished copying .amber files and trimming CSVs into weak_HSA / weak_OBE under GPU directories.")
