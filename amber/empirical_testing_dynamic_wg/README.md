# Dynamic workgroup (dynamic_wg) Amber tests

This directory contains scripts and pre-generated **Amber compute tests** for experimenting with GPU subgroup/workgroup
behaviour, with support for running the *same* test using different numbers of workgroups.

The key idea is to generate `.amber` files as **templates** containing placeholders:

- `NUMWORKGROUPS` (used in the `RUN test_pipe ...` line)
- `TOTALTHREADS` (used in the `EXPECT ... EQ ...` line)

Then, at runtime, instantiate the template with a user-provided workgroup count and run Amber.

## Directory structure

- `ALL_tests_flat/`: input tests in `.txt` format (one file per test).
- `src/`: generators + helper scripts
  - `amber_test_generation.py`: generate `.amber` **templates** from `.txt` inputs.
  - `amber_template_runner.py`: instantiate a template (replace placeholders) and run `amber`.
  - `configuration.py`: configuration object used by generators.
- `test_amber/`: batch generation harness + pre-generated suites
  - `template_test_suite/`: pre-generated **template** `.amber` tests (contains `NUMWORKGROUPS`/`TOTALTHREADS`)
  - `results/` and `test_suite/`: pre-generated **concrete** `.amber` tests (typically hard-coded `RUN ... 65532 ...`)

## Run a template with a chosen workgroup count

From repo root:

1) Pick a template `.amber`, e.g.:

- `amber/empirical_testing_dynamic_wg/test_amber/template_test_suite/output0/0_txt_round_robin.amber`

2) Run it with a desired number of workgroups:

```sh
python3 amber/empirical_testing_dynamic_wg/src/amber_template_runner.py \
  amber/empirical_testing_dynamic_wg/test_amber/template_test_suite/output0/0_txt_round_robin.amber \
  --workgroups 32 \
  -- -v 1.2 -t spv1.5
```

Notes:
- Arguments after `--` are passed directly to the `amber` executable.
- The runner computes `TOTALTHREADS = NUMWORKGROUPS * local_size_x` by parsing `layout(local_size_x = N, ...)` in the
  template’s shader.
- The runner writes an instantiated `.amber` to a temp file, runs `amber`, then deletes the temp file.
  Use `--keep-temp` if you want to inspect it.
