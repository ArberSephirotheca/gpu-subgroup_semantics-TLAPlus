name=""
count=0

while getopts ":n:c:" opt; do
  case $opt in
    a) android=$OPTARG ;;
    s) serial=$OPTARG ;;
    d) device=$OPTARG ;;
    \?) echo "Invalid option -$OPTARG" >&2; exit 1 ;;
  esac
done

bash prep_dir.sh
if [ "$android" ]; then
    if [ "$serial" ]; then
        python3 amber_launch_tests.py --android --serial "$serial"
    else
        python3 amber_launch_tests.py --android
    fi
elif [ "$device" ]; then
    python3 amber_launch_tests.py --device "$device"
else
    python3 amber_launch_tests.py 
fi
python3 amber_launch_tests.py 
bash cleanup.sh


