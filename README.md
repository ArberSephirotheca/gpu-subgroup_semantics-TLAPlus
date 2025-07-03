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

## Example:
`earthly -i +tlaplus-image --INPUT example_shader_program/producer_consumer.comp --OUT=all`

## Command Line Option
- *format*: text, dot, all

## Litmus tests
We also provides part of litmus tests implemented by Tyler Sorensens, available at https://github.com/tyler-utah/AlloyForwardProgress.
For convenience, a special command is available to run all the litmus tests:
```
earthly +tlaplus-image --LITMUS_TESTS TRUE
```
This command will try to run all the litmus tests in the `litmus_tests` directories.


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
