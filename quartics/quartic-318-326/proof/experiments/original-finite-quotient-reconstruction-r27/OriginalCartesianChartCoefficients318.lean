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
  exact IsIntegralHom.SpecMap_iff.mp inferInstance

include H in
lemma ringMap_dominant : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom f) ≫ JLineAtlas318.chart ℚ 1) := by
    rw [H.w]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ (JLineAtlas318.chart ℚ 1)

local instance quotientAlgebra : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
local instance polynomialAlgebra : Algebra R Y.functionField :=
  ((algebraMap (RatFunc ℚ) Y.functionField).comp (algebraMap R (RatFunc ℚ))).toAlgebra
local instance chartAlgebra : Algebra A Y.functionField := ActualOpenFractionField318.sourceAlgebra j
local instance coefficientAlgebra : Algebra R A := f.toAlgebra

/-- The canonical projective coordinate equals the OLD chart's coefficient
embedding, for every polynomial. -/
lemma base_coefficient (q : R) :
    letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1);
    OriginalProjectiveFunctionCoordinate318.κ (algebraMap R (RatFunc ℚ) q) =
      algebraMap R B.functionField q := by
  letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1)
  apply (ActualOpenFractionField318.genericEquiv (JLineAtlas318.chart ℚ 1)).injective
  exact (OriginalProjectiveFunctionCoordinate318.coefficient q).trans
    ((ActualOpenFractionField318.genericAlgEquiv (JLineAtlas318.chart ℚ 1)).commutes q).symm

include H in
/-- The actual Cartesian coefficient map, not a supplied abstract tower. -/
theorem coefficient_square (q : R) :
    algebraMap R Y.functionField q = algebraMap A Y.functionField (f q) := by
  letI := ringMap_dominant p j f H
  have h := OpenFunctionFieldSquare318.on_coefficient j (JLineAtlas318.chart ℚ 1) p f H.w.symm q
  calc
    algebraMap R Y.functionField q =
        (DominantFunctionField318.map p).hom
          (OriginalProjectiveFunctionCoordinate318.κ (algebraMap R (RatFunc ℚ) q)) := rfl
    _ = (DominantFunctionField318.map p).hom
        (letI := ActualOpenFractionField318.sourceAlgebra (JLineAtlas318.chart ℚ 1);
          algebraMap R B.functionField q) := congrArg _ (base_coefficient q)
    _ = algebraMap A Y.functionField (f q) := h

include H in
theorem coefficient_tower : IsScalarTower R A Y.functionField :=
  IsScalarTower.of_algebraMap_eq (coefficient_square p j f H)

include H in
theorem coefficient_integral : Algebra.IsIntegral R A := ⟨ringMap_integral p j f H⟩
end OriginalCartesianChartCoefficients318
