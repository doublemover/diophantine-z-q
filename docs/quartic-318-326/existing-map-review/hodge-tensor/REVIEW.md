# Retrospective audit of our existing Hodge and tensor isomorphisms

## Decision

No instance of the Baba–Granath error was found in the **17 named map families in `inventory.json`**, covering 38 already-published Lean source files at commit `dea5d91b63e43d5f3ba9874c64463a0f28ff934b`. These maps have actual two-sided inverse identities, composition of already constructed equivalences, or a valid sheaf-isomorphism criterion applied to the exact map. None of the inspected arguments substitutes injectivity of curve points, equality of dimensions/ranks, or a one-sided section for invertibility.

This is a bounded retrospective mathematical source review, not a declaration that all isomorphisms in the project have been audited. Group-law/chart gluing, function-field and normalization equivalences, arithmetic finite joins and external-source claims are separate review lanes. The current reviewer did not author the Hodge/tensor implementations reviewed here. The report is not an independent re-review of every transitive Mathlib or project dependency.

No defect requiring a patch was found within the stated claims. The unproved extensions below remain unproved; they are not being converted into successes by this audit.

## Exact maps and inverse evidence

### 1. Affine intrinsic differentials and open restriction

`AffineIntrinsicIso318.iso` is an isomorphism from the tilde sheaf of the algebraic Kähler module to the intrinsic universal differential sheaf on the actual `Spec S`. Its forward map is the previously defined `AffineIntrinsicComparison318.comparison`, not an arbitrary replacement. The source explicitly proves both `comparison_inverse` and `inverse_comparison`.

The latter proof legitimately uses an epimorphism cancellation: `comparison_epi` is itself proved. Its proof uses the uniqueness of localized derivations and the sheaf separation axiom on the actual affine basic-open basis. `AffineDerivationExtension318` independently constructs extension to all opens and proves both extension/evaluation identities. Thus global sections are not assumed to determine arbitrary sheaf maps without the derivation/localization argument.

`IntrinsicOpenRestriction318` proves existence and uniqueness of descent for every module sheaf, so its application of `IntrinsicUniversalComparison318.isoOfUniversal` has the required universal-property premise. The latter is a conditional general lemma, not a hidden assertion that a candidate differential object is universal. `iso_D`, `coefficients_comp` and `IntrinsicChartNormalization318.differential` bind the resulting maps to the actual structural morphism and universal derivative.

All these affine/open claims allow arbitrary commutative coefficient rings. No field, reducedness, domain or unstated quasi-coherence assumption is inserted.

### 2. Normalized local frames and the actual global differential frame

`InvariantNormalizedFrames318` rescales a genuine linear equivalence by a **proved unit**. It proves both the normalized value and the inverse image of 1. The chart comparisons retain the original coefficient/algebra structures.

`WeierstrassIntrinsicOverlaps318` compares the actual sections on the full x/finite and finite/infinity intersections via the stated localization routes and full-image theorems. Under unit discriminant, the x/infinity intersection lies in the finite chart, so restricting those two equalities gives the third equality. This is a full-intersection gluing argument, not agreement only on a dense open.

`IntrinsicGlobalFrame318` proves the actual cover, compatibility, and local freeness on **every ambient subopen of each chart**. `ModuleFrameDescent318.isIso_of_cover` uses the resulting sheaf basis, and `gluedMap_isIso` applies it to the actual multiplication-by-glued-section map. `frame_inv_local` fixes its inverse on the prescribed local generators. The local point-cover fact is used only to establish a cover; it is not used as a pointwise criterion for isomorphism.

The global differential-frame result requires a commutative base and unit discriminant. It does not require a domain.

### 3. The one-sided splitting is not misrepresented as an isomorphism

`StructurePushforwardSplit318` proves an actual section/evaluation splitting and a monomorphism. Its conclusion stops there. This is an important negative control for the error class under review: the code does **not** infer that `O_Y → p_*O_X` is invertible merely because a section exists.

The later upgrade uses additional hypotheses. `IntegralRetraction318` proves injectivity of the retraction from integrality and a domain target, then proves bijectivity of the original ring map. `ProperAffineSections318` obtains integrality on each actual affine base open from universal closedness, handles the empty-open case, and uses the actual section for the retraction. It then detects the sheaf isomorphism on the full affine basis. A bijection on global functions alone is not substituted for this argument.

For the actual completed family, this structure-descent theorem has a domain-base hypothesis.

### 4. The Hodge result concerns the existing canonical evaluation

`IntrinsicHodgeComparison318.hodgeToIdentity` is defined from the actual adjunction, structural morphism and infinity section. At that stage it is a map, not an unconditional isomorphism.

`HodgeInvertibilityCriterion318` proves invertibility of this same evaluation when the actual structure unit is invertible and the actual differential sheaf has a frame. Its proof uses the adjunction triangle identity and naturality. `DomainHodgeComparison318` supplies structure descent for a domain base. `IntrinsicHodgeIsomorphism318` supplies the proved global frame. Finally, `hodgeToIdentityIso_hom` states by reflexivity that the produced isomorphism's forward map is exactly the pre-existing canonical evaluation.

This rules out a superficially similar but insufficient argument: neither the existence of two free rank-one modules nor an arbitrary isomorphism between them establishes the desired canonical map. The inspected source proves invertibility of that map itself.

The complete Hodge claim assumes a domain and unit discriminant. `LiteralIntrinsicHodge318` proves the domain condition for its literal localized base when `N ≠ 0`; its Hodge isomorphism does not silently include `N = 0`. The identity cotangent frame is separately tied to the actual infinity chart and does not assume the Hodge conclusion.

### 5. Tensor transport and contact restrictions

`TensorScalarIso318` starts with an actual ring equivalence. Its semilinear identity equivalences have both inverse identities; its tensor equivalence is constructed from tensor congruence and preserves the specified pure tensors. It does not assert that arbitrary extension of scalars is an isomorphism.

`IntrinsicTensorSheaf318` uses sheafification of the pointwise tensor presheaf. `OpenSheafification318` identifies the actual comparison with the standard open-restriction/sheafification isomorphism on underlying sheaves, then reflects invertibility. `TensorOpenRestriction318` uses the actual open immersion's coefficient-ring equivalence and proves naturality by tensor induction. `TensorSheafFunctor318.unitIso` is the tensor-unit isomorphism followed by the sheafification counit.

`ContactTensor318` constructs actual presentation/base-change equivalences and verifies their generators. Its `contact_square` is equality of full algebra homomorphisms. Crucially, the contact map itself is only an `AlgHom`; it is not declared an isomorphism at a branch point.

`EtaleDifferentialFrame318.ofAlgEquiv` has explicit two-sided inverse proofs using the differential functor's composition identity. `ofFormallyEtale` uses the actual formally étale Kähler base-change equivalence. The contact branch frames use the genuine ramified root coordinate, not the invalid coordinate t at its branch. `SourceBranchLocalization318.sourceLocalizationEquiv` is tied to the actual localization and satisfies its source-map identity. `ContactIntrinsicDifferentials318` then identifies the actual complete normalization's restricted differential sheaf with these chart sheaves, with exact derivative formulas.

`ContactBicanonicalSheaf318.localFrame` is a composition of those actual restriction, tensor-congruence and tensor-unit isomorphisms. It trivializes the actual tensor square **locally** on each of five proved covering charts. It does not produce a global trivialization.

## Claim boundaries and prose consistency

The reviewed packet READMEs accurately distinguish the following stages:

- The old affine packet proved the affine comparison and a conditional Hodge criterion; it did not yet claim a global differential frame.
- The open-restriction and domain-Hodge packets retained their respective missing global-frame step. The later global-gluing packet actually discharges that step.
- The final global differential frame permits arbitrary commutative bases with unit discriminant. The final Hodge isomorphism additionally requires a domain.
- The tensor packet explicitly calls `q0` and `q1` local sections. Their published rational-section identification and whole-intersection gluing are not supplied by these definitions.
- These results do not by themselves identify the contact source with a PEL/modular object, prove a global Kodaira–Spencer comparison, establish a metric normalization, or construct the final `RefinedGeometricRealization`.

No missing witness was found for the claims actually made in this lane. The stronger statements just listed are missing or separately scoped work, not isomorphisms certified by this audit.

## Evidence and reproducibility

`inventory.json` records 17 claim families with concrete objects, maps, assumptions, inverse/isomorphism witnesses, exact-map normalization and boundaries. `source-manifest.json` records the 38 source hashes and declaration line locators, six read prose artifacts and 11 matching historical receipt records. All 38 source files match at least one retained source-hash-bound receipt. These include the historical 9-module affine, 22-module global-gluing and 8-module tensor strict-replay packets.

`binding-check.json` records 120 successful source/evidence and named-declaration checks. `build_inventory.py` reproduces these **identity checks only**. It is not a theorem prover or a general isomorphism certifier. Source reading and the mathematical arguments above provide the separate review judgment.

No Lean build, dependency installation, shared repository edit or broad replay was performed for this audit. Historical strict kernel/recursive-axiom results are retained evidence, not a new local compilation claim. The checkpoint separately reports the hosted full 1,083-module run succeeded at `0e5ff6e`, with proof sources unchanged through this reviewed commit; that run is not substituted for this exact-map review.

## Protocol coverage

For each family the inventory identifies: (1) the actual objects, (2) the required domain/hypotheses, (3) the constructed map, (4) its inverse or valid invertibility criterion, (5) both directions or the criterion that supplies them, (6) coefficient/convention normalization, (7) comparison to the actual downstream map, (8) evidence/source identity, and (9) remaining scope. A claim inventory is not an assertion of exhaustive coverage outside the named lane.
