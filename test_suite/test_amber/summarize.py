import os
import csv
from collections import defaultdict

# Root directory containing GPU folders
root_dir = './'  # Change this if needed

# GPU directories to process
gpu_dirs = ['cezanne_radeon_vega', 'intel_iris_xe_graphics', 'rtx_4070']

# Output file
output_csv = 'gpu_test_summary.csv'

# Gather data
data = []

for gpu in gpu_dirs:
    gpu_path = os.path.join(root_dir, gpu)
    if not os.path.isdir(gpu_path):
        continue

    for sub in sorted(os.listdir(gpu_path)):
        output_dir = os.path.join(gpu_path, sub)
        if not os.path.isdir(output_dir):
            continue
        # Look for the CSV file in the output directory
        for file in os.listdir(output_dir):
            if file.startswith('simple_final_results-') and file.endswith('.csv'):
                passes = 0
                fails = 0
                failed_tests = []
                csv_path = os.path.join(output_dir, file)

                with open(csv_path, newline='') as csvfile:
                    reader = csv.reader(csvfile)
                    next(reader)  # Skip header

                    for row in reader:
                        if row[0].startswith('variant_'):
                            if all(r.strip() == 'P' for r in row[1:]):
                                passes += 1
                            else:
                                fails += 1
                                failed_tests.append(row[0])
                data.append([gpu, sub, passes, fails, ';'.join(failed_tests)])
                break  # Only one result CSV per output directory

# Write summary to CSV
with open(output_csv, 'w', newline='') as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow(['GPU', 'Output Directory', 'Passes', 'Fails', 'Failed Tests'])
    writer.writerows(data)

print(f"Summary written to: {output_csv}")
