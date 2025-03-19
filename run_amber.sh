for file in amber_results/results/output*/*.amber; do
  echo "Running $file"
  amber -d -t spv1.5 "$file"
done