# gpu-subgroup-semantics-TLAPlus

## Pre-requisites
- [Docker](https://docs.docker.com/install/) or [Podman](https://github.com/containers/podman/blob/main/docs/tutorials/podman_tutorial.md)
- [Git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)
- [Earthly](https://earthly.dev/get-earthly)

## Get Started
First, clone the repo including submodule
```bash
git clone --recurse-submodules git@github.com:ArberSephirotheca/gpu-forward-progress-TLAPlus.git
```
Make sure you've started the docker service
```bash
systemctl service docker start
```
And run earthly bootstrap (this step is only necessary the first time)
```bash
earthly bootstrap
```
Then, run following to see the output
```bash
earthly +tlaplus-image --INPUT=<glsl compute file> --OUT=<format>
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
`earthly -i +tlaplus-image --INPUT example_shader_program/synchronization/cm.comp --OUT=text`

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
earthly +tlaplus-image --INPUT <shader.glsl> --OUT=<format>
```
This runs `glslang` to generate SPIR-V, passes it to `Homunculus/src/main.rs` to produce TLA+ modules, and finally invokes TLC to model-check.


## Code Map

- `forward-progress/validation/MCProgram.tla`
  - Declares the top-level `DynamicNodeSet` and the shape of each dynamic-block record (including its embedded SIS, merge stack, and thread set) mirroring Sec. 3.
  - Defines the instruction partitions used to instantiate the CM/SM/SCF/SSO variants (Table 1), together with helper predicates such as `IsCollectiveInstruction` and `IsSynchronousInstruction`.
  - Implements the dynamic-block evolution rules (e.g., `BranchUpdate`, `BranchConditionalUpdateSubgroup`, merge-stack helpers) that create child dynamic blocks and maintain the reconvergence rule described in SIMT-Step Sec. 4.
- `forward-progress/validation/MCThreads.tla`
  - Contains the thread-level state machine: `ExecuteInstruction` dispatches to instruction handlers for memory ops, collective control flow (`OpBranchCollective`, `OpLabelCollective`, etc.), and subgroup operations.
  - Manages per-workgroup snapshots, updates SIS flags, and invokes the branch helpers in `MCProgram` (`BranchUpdate`, `BranchConditionalUpdateSubgroup`) whenever control flow advances so that `DynamicNodeSet` remains consistent with the SIMT-Step reconvergence rules.
- `forward-progress/validation/MCProgressModel.tla`
  - Instantiates `MCProgram`/`MCThreads`, adds the scheduler variables (`fairExecutionSet`, `selected`, `runningThread`), and defines `Step`/`Next` for TLC.
  - Encodes fairness via the `Fairness` predicate and liveness goals such as `EventuallyAlwaysTerminated`.
  - Serves as the entry point for TLC (`Spec`) referenced by `MCProgressModel.cfg`.

**Generated per-program artifacts**
- `forward-progress/validation/MCProgram.tla` – Overwritten by the pipeline with the program-specific instruction partitions, CFG, and dynamic-block metadata derived from the shader.

**Frontend pipeline**
- `example_shader_program/` – Annotated GLSL compute shaders used as reviewer-friendly fixtures; pragmas encode scheduler/subgroup/synchronization settings.
- `Homunculus/src/main.rs` & `compiler/src/codegen/*` – SPIR-V → TLA+ translation: parses `glslang` output, builds CFG/dynamic blocks, and emits the generated `MCProgram.tla` specialised to the shader while relying on the hand-authored `ProgramConf.tla` constant interface.
- `build/output.txt` – Sample TLC output from the provided Earthly target (helpful for confirming end-to-end execution).
