# Actual fine-level modular freeness and quotient fibers

Strict-kernel PASS: 27 declarations in 3 modules, including 14 public theorems. The recursive audit permits only propext, Classical.choice and Quot.sound. All objects are actual Mathlib matrices, upper-half-plane points and orbit quotients.

## Fixed-point producer

`FixedPointTrace318.fixed_equations` derives the two real equations from the actual complex fixed-point equation. For a real matrix of determinant one, fixing z in the upper half-plane implies the exact identity

    trace(g)^2 + 4*c^2*(Im z)^2 = 4.

This proves -2 <= trace(g) <= 2. At trace two the identity and Im z > 0 force c=0; the other fixed-point equations and trace force a=d=1 and b=0. No torsion classification or stabilizer theorem is assumed.

`GammaOneFree318.trace_congruence` uses the actual Mathlib Gamma1(N) membership equations. The integer 2-trace is divisible by N and lies between zero and four. For N>=5 it is therefore zero. `eq_one_of_fixed`, `no_fixed_point` and `subgroup_fixed_iff` prove actual fixed-point freeness and trivial stabilizers for this exact group.

This statement is deliberately about Gamma1(N), N>=5. It does not assert freeness for arbitrary intermediate Gamma_H, for scalar diamond quotients, or for lower levels, which may retain stabilizers.

## Actual Petersson orbit fibers

`GammaOneFiber318.positiveMatrix` maps the actual Gamma1(N) subgroup into GL2+(R); `image` is its genuine range subgroup. `image_fixed_eq_one` transfers the proved freeness to that image.

The existing actual inverse-derivative-squared fiber action and actual orbit quotient are used unchanged. `fiberParam_surjective` proves that every quotient fiber has a representative above any chosen lift of its base point. `fiberParam_injective` proves uniqueness when that lift has trivial stabilizer. Hence `coefficientEquiv` is an actual equivalence between the complex numbers and the exact fiber of the genuine projection over the orbit of z. `coefficientEquiv_norm` identifies the descended Petersson norm with the already proved coordinate norm.

This constructs actual orbit fibers and their coefficients, not an asserted line bundle. Quotient local triviality, a manifold/complex atlas, compactification, an arithmetic model and identification with the manuscript's chosen fine-level geometry remain explicit downstream work. No continuity of the inverse fiber parametrization is claimed here.

## Replay

Run `bash gamma-one-free-action/build-all.sh` from the parent directory. Every accepted module is rebuilt with `-Ddebug.skipKernelTC=false` before the exhaustive declaration audit. Lean 4.35.0 and Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679 are unchanged. One official cached Mathlib module, Analysis/Complex/UpperHalfPlane/FixedPoints, was fetched from the pinned cache without changing sources. No Git/repository files were changed.
