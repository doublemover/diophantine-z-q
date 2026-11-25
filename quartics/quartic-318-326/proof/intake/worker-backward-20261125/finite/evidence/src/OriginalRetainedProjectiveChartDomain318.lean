module

public import OriginalRetainedProjectiveRatio318

@[expose] public section
noncomputable section

namespace OriginalRetainedProjectiveChartDomain318

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedProjectiveRatio318
attribute [local instance] MvPolynomial.gradedAlgebra

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The underlying point of the same Spec(C) used in the algebraic
construction, not an arbitrary ambient projective coordinate. -/
def complexPointZero : T :=
  (⟨(⊥ : Ideal ℂ), inferInstance⟩ : PrimeSpectrum ℂ)

variable (v : κ → ℂ) (i : κ) (hi : v i ≠ 0)

include hi in
private theorem invertible_ith : IsUnit (MvPolynomial.aeval v (MvPolynomial.X i : MvPolynomial κ ℂ)) := by
  rw [MvPolynomial.aeval_X]
  exact isUnit_iff_ne_zero.2 hi

include hi in
/-- The pulled-back D₊(Xⱼ) is exactly the actual nonzero-ratio condition.
This proves the direction that cannot follow from applying R184 only
after both slots have already been assumed invertible. -/
theorem domain_on_actual_point (j : κ) :
    actualPointFromVector v i complexPointZero ∈
      Proj.basicOpen (Grading κ) (MvPolynomial.X j) ↔ v j ≠ 0 := by
  let f : MvPolynomial κ ℂ := MvPolynomial.X i
  let g : MvPolynomial κ ℂ := MvPolynomial.X j
  have hf : f ∈ Grading κ 1 := variable_degree_one κ i
  have hg : g ∈ Grading κ 1 := variable_degree_one κ j
  have hu : IsUnit ((MvPolynomial.aeval v).toRingHom f) := invertible_ith v i hi
  let φ := evaluate (MvPolynomial.aeval v).toRingHom f hu
  let w := Spec.map (CommRingCat.ofHom φ) complexPointZero
  let t := Away.isLocalizationElem hf hg
  rw [actualPoint_via_homogeneous v i hi]
  change w ∈ (Proj.awayι (Grading κ) f hf (by decide) ⁻¹ᵁ Proj.basicOpen (Grading κ) g) ↔ _
  rw [Proj.awayι_preimage_basicOpen hf (by decide : 0 < (1:ℕ)) hg (by decide : 0 < (1:ℕ)),
    PrimeSpectrum.mem_basicOpen]
  change t ∉ Ideal.comap φ ⊥ ↔ v j ≠ 0
  have value : φ t = v j * (v i)⁻¹ := by
    unfold t
    change evaluate (MvPolynomial.aeval v).toRingHom f hu
      (Away.mk (Grading κ) hf 1 (g^1) _) = _
    rw [evaluate_mk _ _ _ _ _ _ _ (v i)⁻¹]
    · simp [g]
    · change MvPolynomial.aeval v f * (v i)⁻¹ = 1
      rw [f,MvPolynomial.aeval_X,mul_inv_cancel₀ hi]
  rw [Ideal.mem_comap,Submodule.mem_bot,value]
  exact mul_ne_zero_iff_right (inv_ne_zero hi)

include hi in
/-- In particular, the actual choice of affine chart is characterized
by the same homogeneous slot rather than an independent norm test. -/
theorem chart_range_iff (j : κ) :
    actualPointFromVector v i complexPointZero ∈ Set.range (affineArrow κ j) ↔ v j≠0 := by
  change actualPointFromVector v i complexPointZero ∈ (affineArrow κ j).opensRange ↔ _
  rw [affineArrow_range]
  exact domain_on_actual_point v i hi j

end OriginalRetainedProjectiveChartDomain318
