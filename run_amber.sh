for file in build/results/output*/*.amber; do
  echo "Running $file"
  amber -d -t spv1.5 "$file"
done