# Actual admissible level-three quotient covering

Status: hosted strict compilation and recursive new-declaration audit PASS, 19 declarations across two source modules. This is source-author evidence, not independent mathematical acceptance or accepted-manifest promotion. The original pending intake is preserved byte for byte; this receipt records its later result.

## Exact statement and objects

The source is the existing `ModularArithmeticCoordinates318.Locus`, the upper-half-plane locus with genuine j different from 0 and 1728. The target is the existing admissible subtype `ThreeArithmeticQuotient318.Source`. The map is the already constructed `sourceProjection`, not a newly selected quotient. The acting group is the actual positive-matrix image `GammaOneFiber318.image 3` of Gamma1(3).

`AdmissibleStabilizer318.gamma_one_fixed` proves any Gamma1(3) matrix fixing an admissible period is the identity. `AdmissibleQuotientCover318.covering` proves `IsQuotientCoveringMap sourceProjection (image 3)`. `localHomeomorph` is its direct consequence.

## Application checks

1. Exact source and statement: the pinned Mathlib quotient-cover theorem requires a quotient map, proper discontinuity, local compactness, and equality of map fibers with group orbits, together with the free action. These are constructed for this map and locus.
2. Quantifiers: every admissible period and every actual Gamma1(3) element; no chosen fundamental-domain or representative assumption.
3. Hypotheses: both excluded j values supply the genuine canonical weight-two scale nonvanishing. Scale transformation gives denominator squared one; positive imaginary part forces the lower-left entry zero. Determinant and fixed-point equations give equal diagonal entries of square one; Gamma1(3) excludes minus one.
4. Maps: the locus action is the restricted actual upper-half-plane action. Its group laws and continuity are inherited. The source projection is unchanged.
5. Inverses/fibers: no unproved bijection is used. `projection_fibers` constructs both implications via the actual orbit quotient and subtype equality.
6. Local/topological hypotheses: openness comes from actual admissibility being locally persistent; local compactness follows. Proper discontinuity is inherited by mapping compact subsets under the subtype inclusion, with the precise intersection witness constructed.
7. Conventions and normalization: level is literally three, not a generic N or the global N-at-least-five freeness theorem. The central minus identity is excluded in Gamma1(3); the result is confined to the admissible locus.
8. Downstream consumer: this covering supplies the previously missing free local-source input for a genuine level-three complex atlas. That atlas and comparison with the literal quartic implicit-function charts remain to be constructed. Merely transporting a complex structure across a homeomorphism would not establish analytification.
9. Independent scope: no cusp extension, holomorphic transition proof, scheme analytification, full arithmetic result, or D210 PEL/Jacobian-family identification is claimed. The separate topological arithmetic comparison and genuine j-immersion packets remain experimental at this cutoff.

## Hosted evidence

Run https://github.com/doublemover/diophantine-z-q/actions/runs/42454181715 at commit 0c83e02896bb8b2b5e286dcdcb657a9911dec383, job 128650010219, artifact 13606474341. Both source checks and ExperimentAudit exit zero. RESULT records Lean 4.35.0, 19 declarations, two modules, and 188 verified predecessor modules reused. The packet checks source/import hashes, uses a fresh output directory and strict kernel checking, and recursively admits only propext, Classical.choice, Quot.sound. It explicitly sets new_source_acceptance and full_arithmetic_theorem_proved false. No local replay was substituted for the hosted result.
