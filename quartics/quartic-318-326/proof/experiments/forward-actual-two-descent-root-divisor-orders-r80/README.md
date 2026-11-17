# Homogeneous-to-affine zero-power API repair

Fresh affine78 run43984267651 failed only at the unavailable identifier pow_eq_zero. Replace that proof by expanding the square and eliminating the two identical branches from mul_eq_zero. The original homogeneous solution and all witness formulas are unchanged.

Only one proof site changes. All statements, assumptions, definitions, imports, options and resource limits remain unchanged. All1334 other source bytes and1335-root order are retained, including checked126 arithmetic sources, the four checked norm ingredients, checked modular-root/Qp-residue sources and pending79 squarefree/CRT and centered-root sources.

The repaired affine target remains a one-root closure. No full induction or auxiliary selection layer is added. Source/API review is not Lean acceptance; strict hosted checking remains required.
