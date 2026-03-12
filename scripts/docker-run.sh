#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

IMAGE_NAME="${IMAGE_NAME:-gpu-subgroup-semantics-tlaplus:latest}"
DOCKER_NETWORK="${DOCKER_NETWORK:-host}"
OUT="text"
INPUT=""
LITMUS_TESTS="FALSE"
SKIP_BUILD="FALSE"

usage() {
    cat <<'EOF'
Usage:
  scripts/docker-run.sh --input <shader.comp> --out <text|dot|all|fuzz>
  scripts/docker-run.sh --litmus-tests

Options:
  --input <path>      Input shader path relative to repository root.
  --out <format>      Output mode: text, dot, all, fuzz. Default: text.
  --litmus-tests      Run litmus test mode (requires ./litmus_tests).
  --skip-build        Skip docker image rebuild and reuse existing image.
  --image <name>      Override image name/tag.
  --network <name>    Docker network mode/name (default: host).
EOF
}

fail() {
    echo "error: $*" >&2
    exit 1
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --input)
            [[ $# -ge 2 ]] || fail "--input requires a value"
            INPUT="$2"
            shift 2
            ;;
        --out)
            [[ $# -ge 2 ]] || fail "--out requires a value"
            OUT="$2"
            shift 2
            ;;
        --litmus-tests)
            LITMUS_TESTS="TRUE"
            shift
            ;;
        --skip-build)
            SKIP_BUILD="TRUE"
            shift
            ;;
        --image)
            [[ $# -ge 2 ]] || fail "--image requires a value"
            IMAGE_NAME="$2"
            shift 2
            ;;
        --network)
            [[ $# -ge 2 ]] || fail "--network requires a value"
            DOCKER_NETWORK="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            fail "unknown option: $1"
            ;;
    esac
done

if [[ "${LITMUS_TESTS}" != "TRUE" && -z "${INPUT}" ]]; then
    fail "provide --input for standard modes, or use --litmus-tests"
fi

case "${OUT}" in
    text|dot|all|fuzz|test) ;;
    *) fail "unsupported --out value: ${OUT}" ;;
esac

if [[ -n "${INPUT}" && ! -f "${PROJECT_ROOT}/${INPUT}" ]]; then
    fail "input file not found: ${INPUT}"
fi

mkdir -p "${PROJECT_ROOT}/build"

if [[ "${SKIP_BUILD}" != "TRUE" ]]; then
    docker build --network "${DOCKER_NETWORK}" -t "${IMAGE_NAME}" "${PROJECT_ROOT}"
fi

docker run --rm \
    --network "${DOCKER_NETWORK}" \
    -e OUT="${OUT}" \
    -e INPUT="${INPUT}" \
    -e LITMUS_TESTS="${LITMUS_TESTS}" \
    -v "${PROJECT_ROOT}/build:/output" \
    "${IMAGE_NAME}"
