This directory contains the amber files for progress mitmus tests.
You could also generate the results using command:
```bash
earthly -i +tlaplus-image --OUT=test
```
you will find the results under the `build` directory.
We also provide a shell script named `run_amber.sh` in the project’s root directory, which allows you to run all Amber tests located under the `result` directory at once.