# Exact primary APIs

Mathlib commit56a005855ea17e0b0958f73ec801ae140b0a1679, read at the exact ref.

- Algebra/Module/Projective.lean: Module.projective_lifting_property lifts a linear map through a SURJECTIVE linear map, with the original projective target module.
- LinearAlgebra/TensorProduct/Quotient.lean: TensorProduct.quotTensorEquivQuotSMul P I identifies (S/I) tensor P with P/(I smul top); quotTensorEquivQuotSMul_mk_one_tmul fixes the actual 1 tensor x representative.
- RingTheory/Ideal/Quotient/Operations.lean: Ideal.quotientKerAlgEquivOfSurjective for the actual Algebra.ofId S R and its proved surjectivity.
- RingTheory/Ideal/Span.lean: mem_span_singleton' states x in span{y} iff there exists a with a*y=x. The commutativity conversion is explicit in ring_kernel.
- RingTheory/Ideal/Operations.lean: Submodule.ideal_span_singleton_smul (r)(N) states (Ideal.span{r}) smul N = r smul N.
- Algebra/Module/Submodule/Pointwise.lean: mem_smul_pointwise_iff_exists (m)(a)(S) states m in a smul S iff there exists b in S with a smul b=m.
- RingTheory/Flat/EquationalCriterion.lean: Module.Flat.projective_of_finitePresentation [Flat R M] [FinitePresentation R M] : Projective R M.

The two OriginalLineAffineModel/BaseChange sources are exact PENDING experiment
producers, not baseline-accepted sources. Their original canonical tilde-Gamma
counit, actual original pullback, and literal extendScalars remain the consumed
maps. The producer confirmed unchanged hashes in its latest revision.

Additional exact-ref APIs read for this application:
- Algebra/DualNumber.lean: DualNumber.lift constructs an algebra map from a specified coefficient algebra map and commuting square-zero element. lift_apply_inl and lift_apply_eps retain both generators. algHom_ext and TrivSqZeroExt.algHom_ext' justify both inverse identities.
- RingTheory/TensorProduct/Basic.lean and Maps.lean: original includeLeft, includeRight, lift, lift_tmul and ext retain BOTH scalar-extension factors.
- Algebra/Algebra/Equiv.lean: AlgEquiv.ofAlgHom f g requires f.comp g=id and g.comp f=id, in that order.
- AlgebraicGeometry/Pullbacks.lean: pullbackSpecIso is the literal categorical pullback of both original Spec algebra maps; inv_fst and inv_snd identify its original projections with Spec of includeLeft/includeRight.
- AlgebraicGeometry/AffineScheme.lean: Scheme.isoSpec is asIso X.toSpecGamma for the original affine scheme, not an arbitrary chosen replacement.

Exact GammaSpecAdjunction.lean declaration read at the pinned ref:
```lean
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) → _) := by
  intro f
  use Spec.preimage f
  simp
```
The same file constructs Spec.fullyFaithful from the actual Gamma-Spec
adjunction and its isomorphic counit. The consumer applies this to the ACTUAL
X.isoSpec.inv followed by p, so the recovered map has direction R→Gamma(X).

Additional exact Mathlib Scheme.lean declarations read at the same pinned ref:
```lean
theorem comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop := rfl
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).appTop :=
  SpecΓIdentity.inv.naturality f
```
The latter exact direction is used for BOTH tensor projections, after the
original affineIso inverse map on global sections. It proves the canonical
section map is the same map as the tensor inverse, not merely that the two
rings admit some isomorphism.

Further primary APIs read at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679:
- AlgebraicGeometry/Pullbacks: Scheme.pullback_map_isOpenImmersion preserves
  open immersions in the actual pullback.map; third map is mono.
- CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic: IsPullback.of_right
  cancels the right Cartesian square from the original outer square.
- AlgebraicGeometry/Restrict: Scheme.Hom.isoOpensRange and hom_ι/inv_comp
  identify the literal original inclusion with its entire image; Opens.ι_image_top.
- AlgebraicGeometry/Scheme: app_eq_appLE, appLE_comp_appLE, appLE_map,
  map_appLE, and comp_preimage retain all original coefficient maps.
- AlgebraicGeometry/AffineScheme: IsAffineOpen U is defined as IsAffine U.

Accepted original producer OpenPullbackStructure318.opens_eq identifies the
entire image in the actual Cartesian square, not a selected refinement.
Accepted UnitCocycleSubopens318.transition_reverse proves reversal on every
common subopen. The Bool extensionality consumer uses it on the whole reversed
overlap and uses the actual presheaf identity restriction, including empty opens.

Additional exact declarations read at the SAME pinned Mathlib ref:
AlgebraicGeometry/Morphisms/Affine.lean:
```lean
lemma IsAffineOpen.inf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V)
```
AlgebraicGeometry/Morphisms/Separated.lean:
```lean
protected class Scheme.IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)
```
The original proper/separated rational structure maps and the affine rational
base imply separatedness of the original terminal map by composition.
Its original closed diagonal is affine, so the exact IsAffineOpen.inf input
is supplied for the actual source and all five original targets.

The original accepted LineFrameIsoCocycle.cocycle_eq and LineFrameGauge.equivalent
are read at the exact repository sources. They compare actual original frames
and module-sheaf isomorphisms. Their outputs are not abstract cocycle labels.


## Actual square-zero determinant norm and original scalar extension

All declarations below are read at Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679, not inferred from a current-branch name.

RingTheory/NormTrace.lean:
```lean
lemma Algebra.norm_one_add_smul {A B} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (a : A) (x : B) :
    ∃ r : A, Algebra.norm A (1 + a • x) =
      1 + Algebra.trace A B x * a + r * a ^ 2
```
Our coefficient squares to zero, so the final term vanishes; the surviving
coefficient is the OLD multiplication-map trace, with no rank or sign change.

LinearAlgebra/Trace.lean: LinearMap.trace_baseChange says the trace of
f.baseChange A equals algebraMap R A (trace R _ f), under Free/Finite R M.
LinearAlgebra/Charpoly/BaseChange.lean: LinearMap.det_baseChange gives the
identical determinant square under the same genuine finite-free input.
LinearAlgebra/TensorProduct/Tower.lean: LinearMap.baseChange_tmul identifies
f.baseChange A (a tensor x) with a tensor f x.
RingTheory/Norm/Defs.lean and RingTheory/Trace/Defs.lean: Algebra.norm_apply
and Algebra.trace_apply are the determinant/trace of the ACTUAL lmul map.
The new multiplication theorem proves the original lmul square on all pure
tensors and then all elements by tensor induction before using these APIs.

RingTheory/Norm/Basic.lean:
```lean
lemma Algebra.norm_eq_of_algEquiv [Ring T] [Algebra R T]
    (e : S ≃ₐ[R] T) (x) : Algebra.norm R (e x) = Algebra.norm R x
```
This algebra-equivalence invariance has NO additional Free/Finite premise.
The ring/algebra assumptions on R and S are the enclosing declaration context.
RingTheory/TensorProduct/Maps.lean: Algebra.TensorProduct.commRight and its
commRight_tmul theorem use the actual rightAlgebra instance. We retain this
orientation because the original affine fiber-product model is S tensor Dual R.

LinearAlgebra/FreeModule/Basic.lean: Module.Free.of_equiv transports freeness
along a linear equivalence from its genuinely free source.
RingTheory/Finiteness/Basic.lean: Module.Finite.equiv transports finite generation
along that same equivalence. OriginalDualAlgebraNormTrace.finite_free explicitly
uses these APIs on the SAME tensor swap followed by the SAME original dual
algebra equivalence; it does not install an unrelated epsilon-killing algebra.

The old repository FiniteFreeGenericTransfer.trace_germ/norm_germ identify actual
multiplication-matrix trace/determinant on the ENTIRE inverse-image section ring
with the old generic field transfer. OpenDominantTrace.trace_embedding and
OpenDominantNorm.norm_embedding then identify the new local values with the OLD
all-open regular maps by the original injective target germ.

FifthPrincipalNeighborhood.cover already supplies whole-preimage rank-eight
bases around EVERY fifth target point. For the four character targets the new
CharacterActualPrincipalBasis constructs that cover from the exact old finite,
flat, Dedekind affine chart and generic degree-eight producers, then applies
FiniteFlatPrincipalBasis.exists_basis_of_rank and AffinePrincipalBasis.basis.
No unramified, nonbranch, finite-only or generically dense restriction is made.


## Genuine full-affine-basis unit-sheaf extension

Fetched and read at SAME56a005855ea17e0b0958f73ec801ae140b0a1679:
Mathlib/Topology/Sheaves/SheafCondition/Sites.lean lines220-255.
For ANY category C, original presheaf F and genuine sheaf F',
```lean
def TopCat.Sheaf.restrictHomEquivHom (h : Opens.IsBasis (Set.range B)) :
  ((inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) ≃ (F ⟶ F'.1)
```
extend_hom_app recovers the SAME original basis components. hom_ext proves
uniqueness from all basis components. Our C is CommGrpCat, B is the ENTIRE
original Scheme.affineOpens inclusion, and target is the genuine pushforward
unit sheaf of the ACTUAL nonreduced thickening. Source is the actual iterated
pushforward from the entire original thickened source. No integral hypothesis
is applied to either nonreduced scheme. Actual integral original X/Y supply
only the OLD norm/trace already constructed on the original reduced schemes.

StructureUnitsSheaf318.isSheaf and pushedUnits are read at the exact accepted
repository sources. They glue both original ring coefficients and inverses,
without assuming the scheme integral. TopCat.Sheaf.pushforward_sheaf_of_sheaf
supplies each actual pushforward sheaf. The old original presheaf section_ext
is used on the target pushed unit sheaf to prove the epsilon square on ALL
opens from its proved affine components. Empty/non-affine opens are not removed.

The original SquareZeroUnit.unit_eq_of_fst, unit_add, unit_injective and map_unit
are read in the exact predecessor. They prove the ACTUAL unit factorization
and its naturality, rather than postulating an isomorphic abstract tangent group.


## Original source comparison and actual pointed-line consumers

No new external theorem is substituted. The exact preceding source definitions
are read again at the source/application/consumer join:
SchemeBoundaryNaturality318.comparison_sectionBoundary retains original
SourceCohomologyComparison.comparison and the actual inverse-image cover.
AffineHOneComparison318.equivalence has that unchanged comparison as forward
map. Its transfer is OLD SheafCohomologyRetraction.transfer composed with its
inverse, not an abstract identification of source H1 with direct-image H1.
MayerVietorisCoefficientNaturality318.sectionBoundary_naturality retains the
same finite-minus-infinity sign and exact terminal integer-sheaf comparison.

UnitCocyclePointedLine318.deformation constructs a genuine original cocycle
module sheaf and the actual pullback special-fiber trivialization from proved
reduction-one transitions. DualNumberPointedKernel318.class_eq_of_iso uses the
actual split zero section to correct a genuine line iso to a pointed iso.
TwoOpenUnitCocycleExt318.ext proves all FOUR transition identities from the
forward edge using original diagonal/reverse/full-overlap cocycle laws.

OriginalHOnePointedEquivalence318.equivalence is the SAME existing whole-H1 map,
now bijective on ALL original pointed lines under its actual affine-overlap
input. Its inverse is used only to SELECT an original representative. The new
norm is defined by genuine norming/gluing of that representative's transitions;
OLD trace enters only in the subsequent norm_classification proof.


## Exact original H1/kernel consumer join

The exact99r9 originalTrace, original trace/8 inverse, actual sumPullback and
matrix statements are read in full. They preserve the actual source H1,
original target schemes, original five quotient pullbacks and original raw
regular traces. No genus, dimension or cross-term assumption is added here.
Their HOSTED elaboration frontier remains separate and is NOT promoted by the
source-level union. All42 shared modules are byte-identical, explicitly hashed.

LineClassPullbackHom318.pullback is the OLD group homomorphism on actual
line-sheaf classes with the OLD tensor law. Its composition theorem and the
actual DualNumberScheme.reduction_map square prove kernel membership for the
new restriction, without conjugating H1 to define the pullback.
OriginalHOneKernelGroupEquivalence318.equivalence is the OLD kernelHom upgraded
by proved bijectivity; source/target subgroup operations remain original tensor.
The two original H1 source constructions are identified through the OLD full
cover-independence theorem, not a chosen new canonical identification.

OriginalFiveHOneTraceEquivalence318.equivalence has original sumPullback forward
and exact original normalized transfers inverse. OriginalFiveHOneNormMatrices
sum_pullback_traces gives raw trace product factor8. This factor is retained
as actual EIGHTH tensor power after the original kernel group homomorphism.
