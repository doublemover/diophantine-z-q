# Actual rotated Gamma1 cusp widths and finite-end coverage

Strict Lean 4.35 replay and exhaustive recursive audit: PASS, 43 declarations in four modules. Standard axioms only.

For every actual g in SL(2,Z), `RotatedWidths318` defines the integer subgroup of n with g*T^n*g^-1 in Gamma1(N). Using only the normality of the principal congruence subgroup Gamma(N), it proves N is a period, constructs a positive natural width w dividing N, and proves the exact translation membership iff w divides n. Gamma1 is never assumed normal.

For N>=5, `RotatedStabilizer318` excludes negative-unipotent elements in this conjugate via the genuine level trace congruence. The genuine imaginary-part transformation shows that a matrix identifying two upper-half-plane points above height1 has lower-left entry zero. Thus the actual conjugated high-region stabilizer consists exactly of the allowed translations.

`RotatedCuspOrbit318.high_orbit_iff_q` proves that two high points have the same genuine rotated Gamma1 quotient image iff their actual width-w exponential coordinates agree. The width is not a supplied cusp-model premise.

`FiniteCuspCoverage318` uses actual finite-index cosets (with the orientation checked by inversion), the actual full modular fundamental domain, and its proved compact truncation. The genuine quotient is a compact core plus finitely many rotated cusp regions. These representatives may repeat a cusp orbit; no distinctness or all-cusp gluing is inferred yet.

Rotated punctured-disc homeomorphisms, identification/gluing of all cusp orbits, compactness of the filled complex source, and its algebraic/arithmetic modular comparison remain downstream.

Run `bash build-all.sh`; the import-all audit checks public, private and generated declaration dependencies with kernel checking enabled.
