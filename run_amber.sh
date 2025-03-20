output_file="amber_results/logs/all_results.log"
mkdir -p amber_results/logs  # Ensure output directory exists
> "$output_file"  # Empty the file if it exists

for file in amber_results/results/output*/*.amber; do
  echo "Running $file" | tee -a "$output_file"
  amber -d -t spv1.5 "$file" >> "$output_file" 2>&1
  echo "Finished $file" | tee -a "$output_file"
  echo "-----------------------------" >> "$output_file"
done