# Actual local different bounds

This packet proves the local different inequalities from Mathlib's actual field trace, trace dual, different ideal, DVR ideal order, and additive valuation. It does not assume Lenstra's coefficient bound.

## Results

1. `LenstraTrace318`: for a nonzero nonunit x of the base domain, the actual trace of 1/(n x) is 1/x and is not integral in the base, where n is the actual field-extension degree.
2. `LenstraDifferent318.different_not_le_degree_mul`: the actual different ideal cannot be contained in the principal ideal (n x). This uses Mathlib's actual codifferent characterization.
3. `LenstraDVR318.different_value_lt`: the actual different-generator value is strictly smaller than v_B(n)+v_B(x).
4. `DVRIntegerValue318.value_nat`: if p is prime and a nonunit in the actual DVR B, v_B(n)=v_p(n) v_B(p) for every positive integer n. The prime-to-p part is proved to be a unit using Bezout and the local-ring axiom.
5. `LenstraVertical318`: the different exponent is the natural value of a generator of the actual different. `different_ideal_eq_pow` identifies the different with the corresponding power of the actual maximal ideal. For p≤d and [L:K]≤d, the exponent is at most 2 v_B(p) floor(log d/log p). `ramified_vertical_bound` gives exactly 2 e e_p floor(log d/log p) when the model identifies v_B(p)=e e_p.
6. `LenstraHorizontal318`: when [L:K] is a unit, the different exponent is at most v_B(x)−1. For a base uniformizer this is the horizontal r≤e−1 coefficient bound.

## Exact scope

The fields and rings are actual Lean types and Mathlib structures. B is the integral closure of the integrally closed base A in the finite separable field extension L/K, with the stated fraction-field towers, and B is a DVR. Characteristic zero is explicit where used. This applies to the completed local extensions used in the geometric argument; this packet does not construct those completions from a scheme.

The remaining geometric realization includes identification of the canonical differential coefficient with the local different exponent, construction of the actual completed local rings, local degree≤cover degree, the branch-prime restriction p≤d, and identification v_B(p)=e e_p. The horizontal statement retains the unit status of the extension degree (as supplied by residue characteristic zero). Regular model, adjunction, section, and projection-formula inputs remain separate.

No claim of the full five-contact theorem or global geometric realization is made. No final local different inequality or detached valuation model is a hypothesis.

## Replay

Run `bash run.sh`. It rebuilds all six modules with `debug.skipKernelTC=false`, then audits every declaration in the six modules recursively. Only propext, Classical.choice, and Quot.sound are allowed. The warnings concern redundant instance parameters and unused section variables, not proof gaps.
