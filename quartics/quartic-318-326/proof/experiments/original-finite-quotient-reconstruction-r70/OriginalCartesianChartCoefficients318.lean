module
public import OriginalCanonicalQuotientBase318
public import OriginalOpenChartGeneric318
public import OpenFunctionFieldSquare318
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public section
noncomputable section
namespace OriginalCartesianChartCoefficients318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "R" => Polynomial ℚ
local notation "B" => ProjectiveJLine318.scheme ℚ
variable {Y : Scheme} [IsIntegral Y] [IsIntegral B]
  (p : Y ⟶ B) [IsDominant p] [IsIntegralHom p]
  {A : Type} [CommRing A] [IsDomain A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (f : R →+* A)
  (H : IsPullback (Spec.map (CommRingCat.ofHom f)) j (JLineAtlas318.chart ℚ 1) p)

include H in
lemma ringMap_integral : f.IsIntegral := by
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom f)) := by
    rw [← H.isoPullback_hom_fst]
    infer_instance
  exact (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom f)).mp inferInstance

include H in
lemma ringMap_dominant : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom f) ≫ JLineAtlas318.chart ℚ 1) := by
    rw [H.w]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ (JLineAtlas318.chart ℚ 1)

/-- Exact named coefficient actions; no hidden-map instance registration. -/
@[instance_reducible] def quotientAlgebra : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
@[expose, instance_reducible] def polynomialAlgebra : Algebra R Y.functionField :=
  (((DominantFunctionField318.map p).hom.comp OriginalProjectiveFunctionCoordinate318.κ).comp
    (algebraMap R (RatFunc ℚ))).toAlgebra
@[expose, instance_reducible] def chartAlgebra : Algebra A Y.functionField :=
  ActualOpenFractionField318.sourceAlgebra j
@[expose, instance_reducible] def coefficientAlgebra : Algebra R A := f.toAlgebra

/-- The canonical projective coordinate equals the OLD chart's coefficient
embedding, for every polynomial. -/
lemma base_coefficient (q : R) :
    letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1);
    OriginalProjectiveFunctionCoordinate318.κ (algebraMap R (RatFunc ℚ) q) =
      algebraMap R (B).functionField q := by
  letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1)
  letI : Algebra R (Spec (CommRingCat.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
  apply (ActualOpenFractionField318.genericEquiv (JLineAtlas318.chart ℚ 1)).injective
  exact (OriginalProjectiveFunctionCoordinate318.coefficient q).trans
    ((ActualOpenFractionField318.genericAlgEquiv (JLineAtlas318.chart ℚ 1)).commutes q).symm

include H in
/-- The actual Cartesian coefficient map, not a supplied abstract tower. -/
theorem coefficient_square (q : R) :
    letI : Algebra R Y.functionField := polynomialAlgebra p
    letI : Algebra A Y.functionField := chartAlgebra j
    algebraMap R Y.functionField q = algebraMap A Y.functionField (f q) := by
  letI : Algebra R Y.functionField := polynomialAlgebra p
  letI : Algebra A Y.functionField := chartAlgebra j
  letI := ringMap_dominant p j f H
  have h := OpenFunctionFieldSquare318.on_coefficient j (JLineAtlas318.chart ℚ 1) p f H.w.symm q
  calc
    algebraMap R Y.functionField q =
        (DominantFunctionField318.map p).hom
          (OriginalProjectiveFunctionCoordinate318.κ (algebraMap R (RatFunc ℚ) q)) := rfl
    _ = (DominantFunctionField318.map p).hom
        (letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1);
          algebraMap R (B).functionField q) := congrArg _ (base_coefficient q)
    _ = algebraMap A Y.functionField (f q) := h

include H in
theorem coefficient_tower :
    letI : Algebra R Y.functionField := polynomialAlgebra p
    letI : Algebra A Y.functionField := chartAlgebra j
    letI : Algebra R A := coefficientAlgebra f
    IsScalarTower R A Y.functionField := by
  letI : Algebra R Y.functionField := polynomialAlgebra p
  letI : Algebra A Y.functionField := chartAlgebra j
  letI : Algebra R A := coefficientAlgebra f
  exact IsScalarTower.of_algebraMap_eq (coefficient_square p j f H)

include H in
theorem coefficient_integral :
    letI : Algebra R A := coefficientAlgebra f
    Algebra.IsIntegral R A := by
  letI : Algebra R A := coefficientAlgebra f
  exact ⟨ringMap_integral p j f H⟩
end OriginalCartesianChartCoefficients318
