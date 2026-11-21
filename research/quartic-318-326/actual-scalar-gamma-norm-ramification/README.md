# The original scalar's sqrt(5)-norm certificate and a shortcut that fails

The [exact paper](ct-original-scalar-gamma-norm-ramification-r1/LITERAL-NORM-SUPPORT-AND-SHIFT-RAMIFICATION.md) gives a positive norm certificate that requires no complete support factorization. It also proves that no norm identity uniform in the original full shifted chart can work, even after the exact original multiplier. An exact local example at 2887 exhibits the obstruction for a *different local input* to that same multiplier. The actual fixed original input instead gives a unit there, and **this is not an obstruction to the fixed original scalar**. Its norm status and rational PointPair remain open.

The [independent review](rc-literal-gamma-norm-ramification-cold-r1/INDEPENDENT-ACTUAL-GAMMA-NORM-RAMIFICATION-REVIEW.md) includes an independent full-point projective replay. All three replays run with standard Python 3 from this folder:

    D=ct-original-scalar-gamma-norm-ramification-r1
    C=rc-literal-gamma-norm-ramification-cold-r1
    python3 -B "$D/replay_variable_shift_2887.py" | cmp - "$D/EXACT-VARIABLE-SHIFT-2887.json"
    python3 -B "$D/replay_crt_norm_receiver.py"   | cmp - "$D/EXACT-CRT-NORM-RECEIVER.json"
    python3 -B "$C/check_independent_projective_2887.py" "$D" | cmp - "$C/EXACT-INDEPENDENT-PROJECTIVE-2887.txt"

No Lean or rank result is claimed.
