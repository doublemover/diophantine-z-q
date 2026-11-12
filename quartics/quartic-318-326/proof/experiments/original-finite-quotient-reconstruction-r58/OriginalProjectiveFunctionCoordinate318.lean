module
public import OriginalGenericStalkNaturality318
public import JLineAtlas318
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public section
noncomputable section
namespace OriginalProjectiveFunctionCoordinate318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "B" => ProjectiveJLine318.scheme ℚ
local notation "R" => CommRingCat.of (Polynomial ℚ)
variable [IsIntegral B]
local instance affineAlgebra : Algebra (Polynomial ℚ) (Spec R).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec R
local instance affineFraction : IsFractionRing (Polynomial ℚ) (Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

/-- The actual standard open contains the original generic point, so its
map is dominant without requiring an unstated typeclass instance. -/
local instance chart_dominant : IsDominant (JLineAtlas318.chart ℚ 1) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  have hc := genericPoint_spec B
  rw [isGenericPoint_def] at hc
  rw [← hc]
  apply closure_mono
  intro y hy
  have he : y = genericPoint B := Set.mem_singleton_iff.mp hy
  subst y
  exact ⟨genericPoint (Spec R), genericPoint_eq_of_isOpenImmersion (JLineAtlas318.chart ℚ 1)⟩

/-- The actual standard affine chart fixes the projective function coordinate. -/
@[expose] def affineCoordinate : (Spec R).functionField ≃ₐ[Polynomial ℚ] RatFunc ℚ :=
  IsLocalization.algEquiv (Polynomial ℚ)⁰ _ _

/-- This coordinate is constructed from the actual generic-stalk map of the
original t-chart, not chosen independently of the projective line. -/
@[expose] def coordinate : (B).functionField ≃+* RatFunc ℚ :=
  (OpenFunctionField318.fieldEquiv (JLineAtlas318.chart ℚ 1)).trans affineCoordinate.toRingEquiv

@[expose] def κ : RatFunc ℚ →+* (B).functionField := coordinate.symm.toRingHom

lemma coefficient (q : Polynomial ℚ) :
    (DominantFunctionField318.map (JLineAtlas318.chart ℚ 1)).hom
      (κ (algebraMap (Polynomial ℚ) (RatFunc ℚ) q)) =
        algebraMap (Polynomial ℚ) (Spec R).functionField q := by
  change (OpenFunctionField318.fieldEquiv (JLineAtlas318.chart ℚ 1))
    ((OpenFunctionField318.fieldEquiv (JLineAtlas318.chart ℚ 1)).symm
      (affineCoordinate.symm (algebraMap (Polynomial ℚ) (RatFunc ℚ) q))) = _
  rw [RingEquiv.apply_symm_apply]
  exact affineCoordinate.symm.commutes q

lemma generic_affine : OriginalGenericStalkNaturality318.generic (Spec R) =
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (Spec R).functionField)) :=
  AlgebraicGeometry.Spec.fromSpecStalk_eq' R _

/-- The projective generic point is in the ORIGINAL polynomial t-chart with
exactly the constructed coordinate map. -/
theorem generic_chart : OriginalGenericStalkNaturality318.generic B =
    Spec.map (CommRingCat.ofHom (κ.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ)))) ≫
      JLineAtlas318.chart ℚ 1 := by
  let f := JLineAtlas318.chart ℚ 1
  haveI : IsIso (DominantFunctionField318.map f) :=
    inferInstanceAs (IsIso (OpenFunctionField318.fieldIso f).hom)
  apply (cancel_epi (Spec.map (DominantFunctionField318.map f))).mp
  rw [← OriginalGenericStalkNaturality318.naturality f, generic_affine,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (coefficient q).symm
end OriginalProjectiveFunctionCoordinate318
