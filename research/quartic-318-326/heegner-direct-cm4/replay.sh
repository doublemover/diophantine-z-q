#!/bin/sh
set -eu
cd "$(dirname "$0")"
book=donors/ACTUAL-ODD2544-MARKED-ORDERS-Q29.json
charts=donors/LOW-48-SUPERSINGULAR-F53.json
eisenstein=donors/eisenstein_representations.py
sha256sum -c SHA256SUMS >/dev/null
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT HUP INT TERM
run() {
    python3 -B calibration/calibrate_direct_cm4.py --book "$book" --charts "$charts" --eisenstein "$eisenstein" "$@"
}
for d in 323 132107 1139 465851; do
    run --d "$d" > "$scratch/$d.json"
    if [ "$d" = 323 ]; then
        cmp "$scratch/$d.json" "calibration/EXACT-CM4-D$d.json"
    else
        run --d "$d" --compact | cmp - "calibration/EXACT-CM4-D$d.json"
    fi
done
python3 -B independent/check_projective_group.py "$scratch" "$charts" | cmp - independent/EXACT-REPLAY.txt
python3 -B calibration/check_production_slice_bounds.py | cmp - calibration/EXACT-DIRECT-CM4-PRODUCTION-COST.json
python3 -B coset-theta/check_trace_zero_cosets.py --book "$book" --calibration calibration/EXACT-CM4-D323.json | cmp - coset-theta/EXACT-FIXED-TRACE-ZERO-LATTICES.json
printf '%s\n' 'Direct CM4 author replay, independent projective replay, production cost checks and fixed coset-lattice checks passed.'
