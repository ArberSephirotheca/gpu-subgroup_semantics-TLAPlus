import os
import re
import shutil
import glob

# Base directories
cadp_root = 'cadp'
amber_root_base = 'empirical_testing/test_amber'
output_prefix = 'output'

# Traverse cadp/<num''>_threads_<num'>_instructions
for cadp_subdir in os.listdir(cadp_root):
    cadp_subdir_path = os.path.join(cadp_root, cadp_subdir)
    if not os.path.isdir(cadp_subdir_path):
        continue

    # Extract <num'> (thread count)
    match_threads = re.search(r'_threads_(\d+)_instructions', cadp_subdir)
    if not match_threads:
        continue
    output_num = match_threads.group(1)
    
    # Path to alloy_output_processed
    alloy_path = os.path.join(cadp_subdir_path, 'alloy_output_processed')
    if not os.path.exists(alloy_path):
        continue

    # Traverse each <num> subdirectory inside alloy_output_processed
    for subdir in os.listdir(alloy_path):
        subdir_path = os.path.join(alloy_path, subdir)
        label_file = os.path.join(subdir_path, f'label_{subdir}.txt')
        if not os.path.isfile(label_file):
            continue

        # Read label content
        with open(label_file, 'r') as f:
            content = f.read()

        # Check if weak HSA or OBE termination passes
        hsa_pass = re.search(r'HSA - Termination: PASS', content)
        obe_pass = re.search(r'OBE - Termination: PASS', content)

        if not (hsa_pass or obe_pass):
            continue  # Skip if both fail

        # Match all GPU directories under test_amber/
        gpu_dirs = glob.glob(os.path.join(amber_root_base, '*'))

        for gpu_dir in gpu_dirs:
            output_dir = os.path.join(gpu_dir, f'{output_prefix}{output_num}')
            if not os.path.exists(output_dir):
                continue

            # Match amber files like <num>_txt_<alphabet>.amber
            for amber_file in os.listdir(output_dir):
                if amber_file.startswith(f'{subdir}_txt') and amber_file.endswith('.amber'):
                    amber_file_path = os.path.join(output_dir, amber_file)

                    if hsa_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_HSA', f'{output_prefix}{output_num}')
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)

                    if obe_pass:
                        target_dir = os.path.join(gpu_dir, 'weak_OBE', f'{output_prefix}{output_num}')
                        os.makedirs(target_dir, exist_ok=True)
                        shutil.copy(amber_file_path, target_dir)

print("✅ Finished copying relevant .amber files into weak_HSA and weak_OBE directories inside each GPU directory.")
