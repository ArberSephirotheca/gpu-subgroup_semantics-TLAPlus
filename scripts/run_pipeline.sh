#!/usr/bin/env bash
set -euo pipefail

OUT="${OUT:-text}"
INPUT="${INPUT:-}"
LITMUS_TESTS="${LITMUS_TESTS:-FALSE}"
WORKDIR="${WORKDIR:-/workdir}"
OUTPUT_DIR="${OUTPUT_DIR:-/output}"

readonly GLSLANG_BIN="glslang/build/install/bin/glslang"
readonly SPIRV_DIS_BIN="glslang/build/install/bin/spirv-dis"
readonly SPIRV_AS_BIN="glslang/build/install/bin/spirv-as"
readonly HOMUNCULUS_BIN="Homunculus/target/release/homunculus"
readonly MC_PROGRAM_PATH="forward-progress/validation/MCProgram.tla"
readonly MC_MODEL_PATH="forward-progress/validation/MCProgressModel"

fail() {
    echo "error: $*" >&2
    exit 1
}

copy_file_to_output() {
    local src="$1"
    local rel_dst="${2:-$1}"
    mkdir -p "${OUTPUT_DIR}/$(dirname "${rel_dst}")"
    cp -f "${src}" "${OUTPUT_DIR}/${rel_dst}"
}

copy_glob_to_output() {
    local pattern="$1"
    shopt -s nullglob
    local files=(${pattern})
    shopt -u nullglob
    for file in "${files[@]}"; do
        local rel="${file#./}"
        copy_file_to_output "${file}" "${rel}"
    done
}

compile_shader() {
    [[ -n "${INPUT}" ]] || fail "no INPUT provided"
    [[ -f "${INPUT}" ]] || fail "input shader not found: ${INPUT}"

    "${GLSLANG_BIN}" -V --target-env spirv1.5 "${INPUT}" -o "${INPUT}.spv"
    copy_file_to_output "${INPUT}.spv" "${INPUT}.spv"

    "${SPIRV_DIS_BIN}" "${INPUT}.spv" > spirv-asm.txt 2>&1 || true
    copy_file_to_output "spirv-asm.txt" "spirv-asm.txt"
}

run_litmus_tests() {
    [[ -d litmus_tests ]] || fail "LITMUS_TESTS=TRUE requires ./litmus_tests"

    mkdir -p litmus_tests_spv litmus_tests_dis litmus_tests_result litmus_tests_mc_programs

    shopt -s nullglob
    local tests=(litmus_tests/*.comp)
    shopt -u nullglob
    [[ ${#tests[@]} -gt 0 ]] || fail "no litmus tests found under litmus_tests/*.comp"

    for test_file in "${tests[@]}"; do
        local name
        name="$(basename "${test_file}" .comp)"

        cp "${MC_PROGRAM_PATH}" "litmus_tests_mc_programs/${name}.tla"
        "${GLSLANG_BIN}" -V --target-env vulkan1.3 "${test_file}" -o "litmus_tests_spv/${name}.spv"
        "${SPIRV_DIS_BIN}" "litmus_tests_spv/${name}.spv" > "litmus_tests_dis/${name}.txt"

        echo "Running test for ${name}"
        "${HOMUNCULUS_BIN}" "litmus_tests_dis/${name}.txt" "litmus_tests_mc_programs/${name}.tla"
        cp "litmus_tests_mc_programs/${name}.tla" "${MC_PROGRAM_PATH}"
        tlc "${MC_MODEL_PATH}" > "litmus_tests_result/${name}.txt" 2>&1 || true
    done

    copy_glob_to_output "litmus_tests_result/*.txt"
}

run_out_test() {
    local amber_test_dir="empirical_testing/test_amber"
    [[ -d "${amber_test_dir}" ]] || fail "OUT=test requires ${amber_test_dir}"

    cd "${amber_test_dir}"
    rm -rf ./results/*
    mkdir -p ../ALL_tests_tmp
    mkdir -p ../ALL_tests_tmp/2_thread_2_instruction
    mkdir -p ../ALL_tests_tmp/2_thread_3_instruction
    mkdir -p ../ALL_tests_tmp/2_thread_4_instruction
    mkdir -p ../ALL_tests_tmp/3_thread_3_instruction
    mkdir -p ../ALL_tests_tmp/3_thread_4_instruction

    cp ../ALL_tests_flat/2t_2i*/*.txt ../ALL_tests_tmp/2_thread_2_instruction/
    cp ../ALL_tests_flat/2t_3i*/*.txt ../ALL_tests_tmp/2_thread_3_instruction/
    cp ../ALL_tests_flat/2t_4i*/*.txt ../ALL_tests_tmp/2_thread_4_instruction/
    cp ../ALL_tests_flat/3t_3i*/*.txt ../ALL_tests_tmp/3_thread_3_instruction/
    cp ../ALL_tests_flat/3t_4i*/*.txt ../ALL_tests_tmp/3_thread_4_instruction/
    python3 amber_launch_tests.py
    rm -rf ../ALL_tests_tmp

    copy_glob_to_output "results/*"
}

run_main_pipeline() {
    compile_shader

    case "${OUT}" in
        text)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            JAVA_OPTS="-Xmx24G -XX:+UseParallelGC" tlc "${MC_MODEL_PATH}" -view -fpmem .25 -workers 20 2>&1 | tee output.txt || true
            copy_glob_to_output "output.*"
            ;;
        dot)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            JAVA_OPTS="-Xmx24G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 20 -dump dot output.dot 2>&1 | tee output.txt || true
            copy_glob_to_output "output.*"
            ;;
        all)
            "${HOMUNCULUS_BIN}" compile ./spirv-asm.txt
            JAVA_OPTS="-Xmx32G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 15 -maxSetSize 100 -dump dot output.dot 2>&1 | tee output.txt || true
            JAVA_OPTS="-Xmx32G" tlc "${MC_MODEL_PATH}" -view -fpmem .50 -workers 15 -maxSetSize 100 > output.txt 2>&1 || true
            copy_glob_to_output "output.*"
            ;;
        fuzz)
            "${HOMUNCULUS_BIN}" fuzz ./spirv-asm.txt
            "${SPIRV_AS_BIN}" --target-env spv1.5 -o fuzz.spv spirv-asm.txt.fuzz.txt
            spirv-cross --version 460 --no-es fuzz.spv --output fuzz.comp
            copy_file_to_output "spirv-asm.txt.fuzz.txt" "spirv-asm.txt.fuzz.txt"
            copy_file_to_output "fuzz.spv" "fuzz.spv"
            copy_file_to_output "fuzz.comp" "fuzz.comp"
            ;;
        *)
            echo "Invalid output format: ${OUT}"
            ;;
    esac
}

main() {
    mkdir -p "${OUTPUT_DIR}"
    cd "${WORKDIR}"

    if [[ "${LITMUS_TESTS}" == "TRUE" ]]; then
        run_litmus_tests
    elif [[ "${OUT}" == "test" ]]; then
        run_out_test
    elif [[ -z "${INPUT}" ]]; then
        echo "No input file provided"
    else
        run_main_pipeline
    fi

    if [[ -f "${MC_PROGRAM_PATH}" ]]; then
        copy_file_to_output "${MC_PROGRAM_PATH}" "MCProgram.tla"
    fi
}

main "$@"
