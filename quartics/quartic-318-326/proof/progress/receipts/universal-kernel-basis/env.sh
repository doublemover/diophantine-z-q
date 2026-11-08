BASE=/workspace/scratch/2cb21e4e0864
source "$BASE/recovery-geometric-0358/independent-pair-rank/env.sh"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_PATH="$HERE:$BASE/recovery-geometric-0358/independent-pair-rank:$LEAN_PATH"
