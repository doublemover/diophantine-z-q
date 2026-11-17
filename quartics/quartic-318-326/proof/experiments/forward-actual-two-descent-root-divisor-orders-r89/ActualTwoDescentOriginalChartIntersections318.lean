module
public import ActualTwoDescentOriginalLocalizedIdealSheafFrames318
public import GenericOpenPushout318
public section
noncomputable section
namespace ActualTwoDescentOriginalChartIntersections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualTwoDescentOriginalTwoChartCubicScheme318
variable {K : Type*} [Field K] [CharZero K]

/-- The literal original common chart is the full scheme intersection. -/
lemma actual_original_intersection_square (n : K) :
    IsPullback (intoAffine n) (intoInfinity n) (affineChart n) (infinityChart n) :=
  GenericOpenPushout318.square _ _
lemma actual_affine_intersection_range (n : K) :
    (affineChart n)⁻¹ᵁ(infinityChart n).opensRange=(intoAffine n).opensRange := by
  ext x
  change (affineChart n x∈Set.range (infinityChart n)) ↔ x∈Set.range (intoAffine n)
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,hz,_⟩ := GenericOpenPushout318.exists_overlap (intoAffine n) (intoInfinity n) x y hy.symm
    exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    exact ⟨intoInfinity n z,congrArg (fun f => f z) (pushout.condition (intoAffine n) (intoInfinity n)).symm⟩
lemma actual_infinity_intersection_range (n : K) :
    (infinityChart n)⁻¹ᵁ(affineChart n).opensRange=(intoInfinity n).opensRange := by
  ext y
  change (infinityChart n y∈Set.range (affineChart n)) ↔ y∈Set.range (intoInfinity n)
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨z,_,hz⟩ := GenericOpenPushout318.exists_overlap (intoAffine n) (intoInfinity n) x y hx
    exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    exact ⟨intoAffine n z,congrArg (fun f => f z) (pushout.condition (intoAffine n) (intoInfinity n))⟩
end ActualTwoDescentOriginalChartIntersections318
