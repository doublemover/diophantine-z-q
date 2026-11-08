BASE=/workspace/scratch/2cb21e4e0864
source "$BASE/recovery-toolchain/proof-environment.sh"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_PATH="$HERE:$HERE/../finite-chart-density:$LEAN_PATH"
