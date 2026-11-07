# 318 local source soundness packet

Read `LOCAL_SOUNDNESS.md` for the final-parameter proof and explicit boundary.
No unconditional `sourceArithmetic` theorem is claimed.

Current fresh audit: **938 declarations, 383 named theorems, 26 modules**, with only `propext`, `Classical.choice` and `Quot.sound`. Exact source and log hashes are in `receipt.json`.

The checked Lean artifacts are:

- `SourcePole318.lean`: actual four-witness pole obstruction, including zeros.
- `LocalSoundness318.lean`: pole/trace/chain composition, exact 4/13 weights,
  contact parameter, torsion-safe identities and local label algebra.
- `RawSourcePole318.lean`: all four pole conclusions from literal stage0 rows.
- `RawReciprocal318.lean`: actual conjugated reciprocal delta parity.
- `RawDetector318.lean`: all literal leaves, every chain recurrence and fold,
  terminal equations, and source-chain nonvanishing.
- `RawWeights318.lean`: literal contact polynomials, scale identities and all
  weight valuations for the three source detectors.
- `ConcretePadic318.lean`: actual embeddings at ±rho into Q_p, the normalized
  valuations, rational coefficient values and the norm identity.
- `SourceContact318.lean`: complete literal-source common-place extraction;
  positivity of R and all16 weighted leaf bounds follow together.
- `SourcePadic318.lean`: that complete extraction at actual split Q_p places,
  including automatic discriminant units and parity of the squared scales.
- `FiniteContact318.lean`: exact finite contact supports, automatic factor and
  delta units, and source-to-common-place extraction at each of the five contacts.
- `CompressedOrientation318.lean`: source-only separation of H and V0 at
  opposite places, using the literal compression and norm tests.
- `RawLucasOrientation318.lean`: actual primary curves, ratios and Lucas residual.
- `ValuationLucasOrientation318.lean`: the source's Lucas residue forces the
  H-positive orientation, without an elliptic reduction/log assumption.
- `SelectedContact318.lean`: final composed detector theorem. At one common
  actual split place all16 leaf bounds hold, H has depth at least8 in reciprocal
  abscissa, and its value at the opposite place is a unit.
- `Audit.lean`: recursive axiom audit of every declaration originating in all 26 modules, including the extensions described below.

Run `bash run.sh` in this workspace. It uses the already pinned Lean 4.35.0 and
Mathlib/component artifacts in sibling `lean-audit`; set `LEAN_AUDIT_ROOT` to a
different audited cache if needed. `debug.skipKernelTC=false` is explicit.
The imported source modules have the source hashes recorded in `receipt.json`.
The new Lean files can also be placed into a Lake package containing the
same pinned concrete/component modules and checked there.

The `generate_*.py` scripts regenerate source-row proofs and definitions
from the pinned IR where needed. They emit proof scripts, not trusted results.
Every emitted identity is subsequently checked by Lean. No dependency on a
custom axiom or sorry is accepted by the audit.

`verification.log` contains the build and full-declaration audit. The JSON
files bind source identities, identify row coverage, and record finite checks.
These finite checks and the checked local theorems do not prove the global
curve, analytic logarithm, height, or completeness inputs listed in the report.

## Actual compressed point

CompressedPoint318 reconstructs the actual finite point H from the literal compression rows and composes this with all three selected-contact theorems. Its coordinates are x=1/f_H, y=A/(k f_H), z=−k/A. At the selected place the source forces v(z)=r≥4, v(x)=−2r and v(y)=−3r; all sixteen leaf bounds hold there. The zero-ordinate and zero-reciprocal-abscissa cases are excluded by the actual equations and positive local depth, not by added guards. This is part of the current 26-module packet.

## Global source points and exact translation

CompressedGlobal318 derives both actual denominator exclusions A≠0 and B≠0 from the literal norm-square row38, using rational nonsquareness of 1/7. It reconstructs H globally and V in its finite branch, and proves z(V)=0 exactly when the allowed V=O chart occurs. CompressedTranslation318 proves H−V=P in the actual Mathlib group for every source assignment. The shift-zero branch and both equal-abscissa tangent branches are included. PrimaryFormal318 reconstructs all four primary points including U=O and decodes the literal ratio rows as z(U_i)=L_i z(H), without asserting that these are already logarithm ratios.

Independent peer reviews, including exact copied source hashes, are in elliptic-three-review, kummer-review, analytic-review and inert-review. The latter certifies the separate inert-place-bridge packet that now constructs the actual split p-adic place from a consumed source contact; it removes the supplied-rho hypothesis in the local selection theorem. Theta-peer-review is a bounded mathematical normalization review, not a kernel formalization.

## Raw alternate factors and oriented root differences

RawAlternatePade318 verifies the literal common G Padé quotient, three J Padé quotients and the order-four linear J factor, all actual ratio rows, and their global nonzero factors. The common logarithm surrogate vanishes exactly when V=O; in that branch all four alternate reciprocal u coordinates vanish. At a consumed contact V=O is impossible, so the quotient denominator is nonzero there. No global inverse guard has been invented.

ReciprocalDifference318 and RawRootDifference318 identify each raw root-square abscissa with the actual oriented group difference U_i−V_i, including either identity-chart branch. AlternateFormal318 extracts the exact positive branch for all four conjugated alternate charts from the unsquared linear leaves: either the identity endpoint u=0,v=1, or v(u)=a≥1 and v(v−1)=4a. These are the precise source hypotheses needed for the separate actual J-series precision theorems.


## Actual reciprocal group addition

ReciprocalDouble318 proves actual Mathlib doubling with the reciprocal rational formulas and handles identity/inverse charts. ReciprocalGroup318 combines these with the analytic worker's independently checked ReciprocalAddition318 secant algebra. Its actual_add theorem proves the full actual group law on the normalized reciprocal branch, including secant, doubling, identity and inverse cases. The secant numerator nonvanishing is derived, not assumed. Explicit normalization premises are constant-one at zero and matching square roots when the squared parameters agree; canonical positive-root uniqueness supplies these in analytic applications. Denominator and output-ordinate nonvanishing are explicit generic-field premises.

This imports ReciprocalAddition318 from sibling padic-tail, whose source hash is recorded in the receipt; its GenericFormalAddition318 dependency closure must be available on LEAN_PATH. run.sh includes the existing pinned padic-tail build cache.

## Independent bounded reviews and remaining analytic scope

The scalar-peer-review directory records an independent exact-source rebuild/audit of the four scalar source/place modules (52 declarations). The global-coset-review directory records four norm-square, transport and literal H/V-label modules (30 declarations). Each review states its retained global hypotheses and hashes all reviewed copies. Earlier anchor, 2-/3-adic, Kummer, inert-place and analytic reviews remain separate and bounded.

Source primary/alternate reciprocal depths can be one. A first logarithm evaluation theorem restricted to depth at least two cannot alone finish those source applications. Scalar contacts may be inert, so a theorem only over Qp cannot silently be applied to the inert quadratic place. The separate inert-completion workspace now proves an actual complete quadratic normed field realization, exact normalized absolute value, isometric Qp embedding and complete integral ring. Neither issue is concealed by an abstract sourceArithmetic premise.

## Uniform branch estimates and torsion-safe index comparison

RestrictedBranch318 proves uniform H error at most norm(p)^3 and B/branch error at most norm(p)^4 for every integral scaled parameter, including units. The constant-one branch is nonzero without requiring D to be a unit. These estimates are consumed by the separate actual depth-one logarithm packet.

TorsionSafeIndex318 proves that H=nP+tau, R=cP and 2tau=0 imply n log(R)=c log(H) for every actual subgroup homomorphism, without placing P in the subgroup. A logarithm-depth gain k then forces p^k to divide c. Both normalized valuation and norm-only versions are checked; the latter applies directly to the actual inert completion. The zero scalar branch is included. This is a composition theorem, not a substitute for constructing the actual logarithm or verifying source-point membership.

Independent dual-square and first-descent reviews are recorded in dual-square-review and first-descent-review. They verify the now unconditional arithmetic interfaces in those separate packets and do not claim global rank or canonical-height construction.
