# gpu-subgroup-semantics-TLAPlus

## Guide for Reviewers

This artifact accompanies *SIMT-Step Execution: A Flexible Operational Semantics for GPU Subgroup Behavior* and is meant to let PLDI reviewers inspect the executable TLA+ model that realises the paper’s operational rules.

- **Dynamic blocks (Sec. 3).** `DynamicBlock` in `forward-progress/validation/MCProgram.tla:307` stores the SIS, thread sets (`currentThreadSet`, `notExecuteSet`, `unknownSet`), block label (`labelIdx`), identifier (`id`), merge stack, and child blocks. The merge target is recovered on branching via `BranchUpdate` (`forward-progress/validation/MCProgram.tla:558`).
- **Instruction classes (Sec. 4/Tab.1).** The CM/SM/SCF/SSO partitions are encoded via `IsCollectiveInstruction` / `IsSynchronousInstruction` in `forward-progress/validation/MCProgram.tla:264-303`.
- **Dynamic-block evolution (Sec. 4).** Independent branching: `BranchUpdate` (`MCProgram.tla:554`), `OpBranch` (`MCThreads.tla:1590`), `OpBranchConditional` (`MCThreads.tla:1671`). Collective branching/labels: `BranchConditionalUpdateSubgroup` (`MCProgram.tla:798`), `OpBranchCollective` (`MCThreads.tla:1545`), `OpBranchConditionalCollective` (`MCThreads.tla:1619`), `OpLabelCollective` (`MCThreads.tla:1866`).
- **Thread-level semantics (Sec. 4).** `MCThreads.tla:1918-2047` contains `ExecuteInstruction`, which dispatches to memory, collective control flow, and subgroup operations.
- **System-level spec (Sec. 4).** `forward-progress/validation/MCProgressModel.tla` assembles the program, threads, and scheduler, defining `Init` and `Next` so TLC checks the same fairness/liveness properties discussed in the paper.
- **Initial state (`Init` in `MCProgressModel.tla`)**
  - `InitProgram` (`MCProgram.tla`) = `InitDB` ∧ `InitGPU`.
  - `InitThreads` (`MCThreads.tla`) set up per-thread PCs/states.
  - `InitScheduler`, `InitState` (`MCProgressModel.tla`) choose the scheduler (HSA/OBE) and initialize scheduler state.
- **Transition relation**
  - `Step` / `Next` (`MCProgressModel.tla`) call `ExecuteInstruction` (`MCThreads.tla`) and `UpdateFairExecutionSet` to advance one ready thread while enforcing fairness.
  - Instruction handlers in `MCThreads.tla` perform the primed assignments; when control flow branches they invoke `BranchUpdate`/`BranchConditionalUpdateSubgroup` from `MCProgram.tla` to evolve the dynamic blocks.


### Worked Example — Collective Control Flow

Consider the T–Label / G–Collective-UBranch rules for CM/SM/SCF:

1. `OpLabelCollective` (`MCThreads.tla:1866`) waits until all threads in the dynamic block are aligned, then bumps their PCs together—mirroring Step–Label.
2. `OpBranchCollective` (`MCThreads.tla:1545`) calls `BranchConditionalUpdateSubgroup` (`MCProgram.tla:798`) which (a) update the thread set in the child dynamic block, (b) pushes merge targets onto the merge stack, and (c) reuses existing children when reconverging at a merge block.

Reviewers who want to follow the execution end-to-end can run `scripts/docker-run.sh --input example_shader_program/synchronization/cm.comp --out text`, open the generated `build/MCProgram.tla`, and observe how the CFG emitted for that shader instantiates these operators.

## Pre-requisites
- [Docker](https://docs.docker.com/install/) or [Podman](https://github.com/containers/podman/blob/main/docs/tutorials/podman_tutorial.md)
- [Git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
- Bash shell

## Get Started
Run the end-to-end pipeline and collect outputs in `build/` (the helper script builds the image automatically unless `--skip-build` is set):
```bash
scripts/docker-run.sh --input <glsl compute file> --out <format>
```

Equivalent raw Docker command (without helper script):
```bash
docker build -t gpu-subgroup-semantics-tlaplus .
docker run --rm \
  --network host \
  -e INPUT=<glsl compute file> \
  -e OUT=<format> \
  -v "$(pwd)/build:/output" \
  gpu-subgroup-semantics-tlaplus
```

If your environment blocks Docker bridge networking, use host networking:
```bash
scripts/docker-run.sh --network host --input <glsl compute file> --out <format>
```

## GLSL
In our version of GLSL, we add additional syntax to take in TLA+ launch configuration
such as **Scheduler**, **subgroup size**, and **number of workgroup**.
You can check out the file under `example_shader_program` for more info.

### Scheduler
you can specify the scheduler for TLA+ model in shader program using following syntax:
```glsl
#pragma scheduler(<scheduler name>)
```
Currently we only support two scheduler: **HSA** and **OBE**
### Subgroup size
you can specify the subgroup size for TLA+ model in shader program similar to how you specify the workgroup size:
```glsl
layout(tla_subgroup_size = <num>) in;
```
num must be a **non-zero positive integer**
### Number of Workgroup
Similarily, you can specify the number of workgroup for TLA+ model in shader program using:
```glsl
layout(tla_num_workgroups = <num>) in;
```
num must be a **non-zero positive integer**.
### Synchronization Model
Select the SIMT-Step model with:
```glsl
layout(tla_synchronization_id = <id>) in;
```
`1` → SSO, `2` → SCF, `3` → SM, `4` → CM.

| `id` | Label | Collective instructions | Synchronous instructions | Independent instructions |
|------|-------|------------------------|--------------------------|--------------------------|
| 1    | SSO   | Subgroup ops (`OpGroup*`) | — | All remaining instructions |
| 2    | SCF   | Subgroup ops + control flow | — | Others |
| 3    | SM    | Subgroup ops + control flow | `OpAtomicLoad`, `OpAtomicStore`, `OpAtomicOr` | Others |
| 4    | CM    | Subgroup ops + control flow + all memory ops | — | Others |

**Limitation.** At present, the synchronous semantics for SM are only modeled for `OpAtomicLoad`, `OpAtomicStore`, and `OpAtomicOr`. Other atomic opcodes (e.g., `OpAtomicAdd`, `OpAtomicSub`, `OpAtomicExchange`) still execute independently; extending the synchronous rules to them is future work.

## Example:
`scripts/docker-run.sh --input example_shader_program/synchronization/cm.comp --out text`

## Command Line Option
- *format*: text, dot, all


## List of supported SPIR-V Instructions
- OpVariable
- OpReturn
- OpLoad
- OpStore
- OpAtomicLoad
- OPAtomicStore
- OpBranch
- OpBranchConditional
- OpSwitch
- OpLabel
- OpLogicalOr
- OpLogicalAnd
- OpLogicalEqual
- OpLogicalNotEqual
- OpLogicalNot
- OpEqual
- OpNotEqual
- OpLess
- OpLessOrEqual
- OpGreater
- GreaterOrEqual
- OpAdd
- OpAtomicAdd
- OpSub
- OpAtomicSub
- OpMul
- OpSelectionMerge
- OpLoopMerge
- OpAtomicExchange
- OpAtomicCompareExchange
- OpGroupAll
- OpGroupAny
- OpGroupNonUniformAll
- OpGroupNonUniformAny
- OpControlBarrier

**Note**:
- The model treats the following instructions as equivalent:
    - `OpStore` and `OpAtomicStore`
- Global variables (e.g. Storage Buffer) are assigned to default values if they are not initialized in the function body.
    - For `uint` and `int` type, the default value is **0**.
    - For `bool` type, the default value is **true**.

## Supported Type
- int
- uint
- bool

## Memory Semantics
The model does not implement any extension to memory semantics, and all SPIR-V instructions
are behaving like `SequentiallyConsistent`.

## Reference
- https://lamport.azurewebsites.net/tla/safety-liveness.pdf


### Workflow Overview

```
scripts/docker-run.sh --input <shader.glsl> --out <format>
```
This runs `glslang` to generate SPIR-V, passes it to `Homunculus/src/main.rs` to produce TLA+ modules, and finally invokes TLC to model-check.

**Generated per-program artifacts**
- `forward-progress/validation/MCProgram.tla` – Overwritten by the pipeline with the program-specific instruction partitions, CFG, and dynamic-block metadata derived from the shader.

**Frontend pipeline**
- `example_shader_program/` – Annotated GLSL compute shaders used as reviewer-friendly fixtures; pragmas encode scheduler/subgroup/synchronization settings.
- `Homunculus/src/main.rs` & `compiler/src/codegen/*` – SPIR-V → TLA+ translation: parses `glslang` output, builds CFG/dynamic blocks, and emits the generated `MCProgram.tla` specialised to the shader while relying on the hand-authored `ProgramConf.tla` constant interface.
- `build/output.txt` – Sample TLC output from the Docker pipeline (helpful for confirming end-to-end execution).
