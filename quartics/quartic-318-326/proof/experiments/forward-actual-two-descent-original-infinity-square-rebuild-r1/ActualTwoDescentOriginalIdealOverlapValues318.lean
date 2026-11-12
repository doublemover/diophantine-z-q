module
public import ActualTwoDescentOriginalOverlapSquareSections318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealOverlapValues318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalInverseInfinityTransition318
universe u
variable {K : Type u} [Field K] [CharZero K]
abbrev overlapEmbedding (n : K) := intoAffine n ≫ affineChart n
abbrev overlapIdeal (n : K) (i : Fin 3) := (originalRootIdealSheaf n i).restrict (overlapEmbedding n)

/-- Untwisted infinity coefficient restriction to the SAME actual
common-chart embedding. The existing pushforward-congruence is retained. -/
def infinityPlainRestriction (n : K) : infinityInversePushed n ⟶ overlapFunctionsPushed n :=
  ClutchedModule318.restriction (infinityChart n) (intoInfinity n) ≫
    (Scheme.Modules.pushforwardCongr (actual_original_overlap_square n)).hom.app _

def affineValue (n : K) (i : Fin 3) : overlapIdeal n i ⟶
    SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).symm
    (affineProjection n i ≫ affineIdealRestriction n i)
def infinityValue (n : K) (i : Fin 3) : overlapIdeal n i ⟶
    SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).symm
    (infinityProjection n i ≫ infinityPlainRestriction n)

/-- The ACTUAL global pullback condition produces whole sheaf-map
matching. This is not an overlap compatibility supplied as a hypothesis. -/
lemma actual_overlap_values (n : K) (i : Fin 3) :
    affineValue n i=infinityValue n i ≫ ClutchedModule318.multiply (inverseUSection n) := by
  apply ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [affineValue,infinityValue,Equiv.apply_symm_apply]
  simpa only [infinityInverseRestriction,infinityPlainRestriction,
    ClutchedModule318.twistedRestriction,Category.assoc] using actual_ideal_sheaf_compatibility n i

lemma actual_overlap_values_apply (n : K) (i : Fin 3) (U : (overlapScheme n).Opens)
    (s : Γ(overlapIdeal n i,U)) :
    (affineValue n i).app U s=(infinityValue n i).app U s*
      ((overlapScheme n).presheaf.map (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op
        (inverseUSection n)) := by
  rw [actual_overlap_values]
  exact ClutchedModule318.multiply_apply _ U _
end ActualTwoDescentOriginalIdealOverlapValues318
