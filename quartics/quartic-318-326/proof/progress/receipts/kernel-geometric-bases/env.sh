BASE=/workspace/scratch/2cb21e4e0864
source "$BASE/recovery-geometric-0358/changed-kernel-product/env.sh"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_PATH="$HERE:$HERE/upstream:$BASE/resumed-completed-addition/upstream:$BASE/resumed-completed-addition:$LEAN_PATH"
