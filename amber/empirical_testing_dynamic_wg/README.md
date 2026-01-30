# Dynamic workgroup (dynamic_wg) Amber tests

This directory contains scripts and pre-generated **Amber compute tests**, with support for running the *same* test using different numbers of workgroups.

The key idea is to generate `.amber` files as **templates** containing placeholders:

- `NUMWORKGROUPS` (used in the `RUN test_pipe ...` line)
- `TOTALTHREADS` (used in the `EXPECT ... EQ ...` line)

At runtime, instantiate the template with a user-provided workgroup count and run Amber.

## Quickstart: run a template with a chosen workgroup count

From repo root:

```sh
python3 amber/empirical_testing_dynamic_wg/src/amber_template_runner.py \
  amber/empirical_testing_dynamic_wg/test_amber/template_test_suite/output0/0_txt_round_robin.amber \
  --workgroups 32 \
  -- -v 1.2 -t spv1.5
```

Notes:
- Arguments after `--` are forwarded to the `amber` executable.
- The runner computes `TOTALTHREADS = NUMWORKGROUPS * local_size_x` by parsing `layout(local_size_x = N, ...)` in the
  template shader.
- The runner writes an instantiated `.amber` to a temp file, runs `amber`, then deletes the temp file.
  Use `--keep-temp` if you want to inspect it.

## Directory structure

- `ALL_tests_flat/`: input tests in `.txt` format (one file per test).
- `src/`: generators + helper scripts
  - `amber_test_generation.py`: generate `.amber` **templates** from `.txt` inputs.
  - `amber_template_runner.py`: instantiate a template and run `amber`.
  - `configuration.py`: configuration object used by generators.
- `test_amber/`: batch generation harness + pre-generated suites
  - `template_test_suite/`: pre-generated **template** `.amber` tests (contains `NUMWORKGROUPS`/`TOTALTHREADS`)
    - `weak_HSA/`, `weak_OBE/`, `weak_fair/`: filtered subsets based on CADP labels; each contains the same suite
      subdirectories (e.g. `weak_HSA/2_threads_3_instructions/`).

## Template format

Templates differ from normal Amber scripts only in that they contain placeholders:

- `RUN test_pipe NUMWORKGROUPS 1 1`
- `EXPECT ... EQ TOTALTHREADS`

`amber_template_runner.py` replaces those placeholders and runs Amber.