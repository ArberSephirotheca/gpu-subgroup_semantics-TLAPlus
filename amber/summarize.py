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

# We'll store the final combined CSVs and summaries in:
results_dir = os.path.join("empirical_testing", "results")
os.makedirs(results_dir, exist_ok=True)

# Track copied files per GPU and variant: which test_ids we copied
# { gpu_dir: { 'weak_HSA': {cadp_subdir: set(test_ids)}, 'weak_OBE': {...} } }
copied_files = {}

# We'll accumulate data for each (gpu, variant) so we can produce a single CSV+TXT at the end
# global_data[gpu_dir][variant] = { 'header': [...], 'rows': [ [subdir, testID, col1, col2, ...], ... ] }
global_data = {}

###############################################################################
# 1) Copy .amber files and collect the test IDs
###############################################################################

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

        # Check for "Termination: PASS" lines
        hsa_pass = re.search(r'HSA - Termination: PASS', content)
        obe_pass = re.search(r'OBE - Termination: PASS', content)
        if not (hsa_pass or obe_pass):
            continue

        gpu_dirs = glob.glob(os.path.join(amber_root_base, '*'))
        for gpu_dir in gpu_dirs:
            amber_test_dir = os.path.join(gpu_dir, cadp_subdir)
            if not os.path.exists(amber_test_dir):
                continue

            # Initialize data structures
            copied_files.setdefault(gpu_dir, {'weak_HSA': {}, 'weak_OBE': {}})
            global_data.setdefault(gpu_dir, {
                'weak_HSA': {'header': None, 'rows': []},
                'weak_OBE': {'header': None, 'rows': []}
            })

            # For whichever passes, record the subdir
            if hsa_pass:
                copied_files[gpu_dir]['weak_HSA'].setdefault(cadp_subdir, set())
            if obe_pass:
                copied_files[gpu_dir]['weak_OBE'].setdefault(cadp_subdir, set())

            # Copy amber files
            for amber_file in os.listdir(amber_test_dir):
                if amber_file.startswith(f'{subdir}_txt') and amber_file.endswith('.amber'):
                    test_id_match = re.match(r'(\d+)_txt', amber_file)
                    if not test_id_match:
                        continue
                    test_id = test_id_match.group(1)

                    amber_file_path = os.path.join(amber_test_dir, amber_file)

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

###############################################################################
# 2) Filter relevant CSV rows per subdir, write local summary, accumulate in global_data
###############################################################################

for gpu_dir, variants in copied_files.items():
    for variant_name in ['weak_HSA', 'weak_OBE']:
        for cadp_subdir, test_ids in variants[variant_name].items():
            amber_test_dir = os.path.join(gpu_dir, cadp_subdir)
            csv_files = glob.glob(os.path.join(amber_test_dir, 'simple_final_results-*.csv'))
            if not csv_files:
                continue

            # We just pick the first CSV
            csv_file = csv_files[0]
            with open(csv_file, newline='') as f:
                reader = list(csv.reader(f))
            if not reader:
                continue

            header = reader[0]
            rows = reader[1:]

            # Filter to only the test IDs we care about
            filtered_rows = [header]
            for r in rows:
                if not r:
                    continue
                if r[0].isdigit() and r[0] in test_ids:
                    filtered_rows.append(r)
                elif r[0].startswith("Total failures"):
                    break

            # If no actual data
            if len(filtered_rows) <= 1:
                continue

            # Write the filtered CSV next to the .amber files
            variant_dir = os.path.join(gpu_dir, variant_name, cadp_subdir)
            os.makedirs(variant_dir, exist_ok=True)
            filtered_csv_path = os.path.join(variant_dir, os.path.basename(csv_file))
            with open(filtered_csv_path, 'w', newline='') as f:
                writer = csv.writer(f)
                writer.writerows(filtered_rows)

            # Create local summary table
            table_header = filtered_rows[0]
            table_data = filtered_rows[1:]
            num_cols = len(table_header) - 1  # ignoring first col (testID) for pass/fail

            fail_counts = [0]*num_cols
            for row in table_data:
                for i in range(num_cols):
                    if len(row) > i+1 and row[i+1].strip() == 'F':
                        fail_counts[i] += 1

            total_failures_row = ["Total failures:"] + [str(fc) for fc in fail_counts]
            table = [table_header] + table_data + [total_failures_row]

            # Write local summary text
            local_summary_txt = os.path.join(variant_dir, "final_summary_table.txt")
            if USE_TABULATE:
                local_table_str = tabulate(table, headers='firstrow', tablefmt='fancy_grid')
            else:
                # minimal fallback
                lines = []
                lines.append(" | ".join(table[0]))
                for drow in table_data:
                    lines.append(" | ".join(drow))
                lines.append(" | ".join(total_failures_row))
                local_table_str = "\n".join(lines)
            with open(local_summary_txt, 'w', encoding='utf-8') as outf:
                outf.write(local_table_str)

            # ========= Accumulate into global_data for this (gpu_dir, variant_name) =========

            # We'll store table_header if not already stored
            if global_data[gpu_dir][variant_name]['header'] is None:
                # We'll prepend "Subdir" to the CSV's columns, so each row is [subdir, TestID, col2, col3...]
                global_data[gpu_dir][variant_name]['header'] = ["Subdir"] + table_header

            for row in table_data:
                # row = [testID, col2, col3, ...]
                combined_row = [cadp_subdir] + row  # e.g. [cadp_subdir, testID, col2, col3...]
                global_data[gpu_dir][variant_name]['rows'].append(combined_row)

###############################################################################
# 3) Write separate CSV+TXT for each GPU+variant *into empirical_testing/results*
###############################################################################

for gpu_dir in global_data:
    for variant_name in ['weak_HSA', 'weak_OBE']:
        hdr = global_data[gpu_dir][variant_name]['header']
        rws = global_data[gpu_dir][variant_name]['rows']
        if hdr is None or not rws:
            # means no rows for that variant
            continue

        # We'll store them in empirical_testing/results
        # Sanitize gpu_dir to a simpler name
        safe_gpu_name = os.path.basename(gpu_dir.rstrip("/"))
        # Build final file paths
        combined_csv_name = f"combined_results-{safe_gpu_name}-{variant_name}.csv"
        combined_csv_path = os.path.join(results_dir, combined_csv_name)

        with open(combined_csv_path, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(hdr)
            writer.writerows(rws)

        # Build big table with final "Total failures:" row
        passfail_start_idx = 2  # ignoring Subdir & TestID => from col2 onward
        num_pf_cols = len(hdr) - passfail_start_idx
        fail_counts = [0]*num_pf_cols

        for row in rws:
            for i in range(num_pf_cols):
                idx = passfail_start_idx + i
                if idx < len(row) and row[idx].strip() == 'F':
                    fail_counts[i] += 1

        total_fail_row = ["Total failures:", ""]  # placeholders for Subdir, TestID
        total_fail_row.extend(str(fc) for fc in fail_counts)

        big_table = [hdr] + rws + [total_fail_row]

        # Now produce combined_summary
        combined_txt_name = f"combined_summary-{safe_gpu_name}-{variant_name}.txt"
        combined_txt_path = os.path.join(results_dir, combined_txt_name)

        if USE_TABULATE:
            table_str = tabulate(big_table, headers='firstrow', tablefmt='fancy_grid')
        else:
            lines = [" | ".join(hdr)]
            for row in rws:
                lines.append(" | ".join(row))
            lines.append(" | ".join(total_fail_row))
            table_str = "\n".join(lines)

        with open(combined_txt_path, 'w', encoding='utf-8') as f:
            f.write(table_str)

print("✅ Done! Per-subdir CSV + local table are in each GPU folder, and final combined files in empirical_testing/results.")
