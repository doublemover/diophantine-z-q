module
public import ContactBicanonicalCoefficients318
public import ReciprocalInfinityBase318
public section
noncomputable section
namespace ContactBicanonicalRatios318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev Branch (i : Fin 4) := ContactBicanonicalCoefficients318.BranchRing c i
abbrev Infinity := InfinityGlobalChart318.InfinityOrder c

/-- The finite projective coordinate is formed from the two actual
coefficients by dividing by the everywhere-unit q0 coefficient. -/
@[expose] def branchRatio (i : Fin 4) : Branch c i :=
  (↑((ContactBicanonicalCoefficients318.branchQ0_unit c i).unit)⁻¹ : Branch c i) *
    ContactBicanonicalCoefficients318.branchQ1 c i

/-- At infinity use q0/q1, dividing only by the everywhere-unit q1 coefficient. -/
@[expose] def infinityRatio : Infinity c :=
  (↑((ContactBicanonicalCoefficients318.infinityQ1_unit c).unit)⁻¹ : Infinity c) *
    ContactBicanonicalCoefficients318.infinityQ0 c

@[expose] def reciprocalCoordinate : Infinity c :=
  algebraMap ℚ (Infinity c) (↑((c 0)⁻¹) : ℚ) *
    (ContactFrameNormalization318.infinityCoordinate c)^2

theorem branchRatio_eq (i : Fin 4) :
    branchRatio c i=ContactBicanonicalCoefficients318.branchT c i := by
  unfold branchRatio ContactBicanonicalCoefficients318.branchQ1
  have h := congrArg (fun x : Branch c i =>
    (↑((ContactBicanonicalCoefficients318.branchQ0_unit c i).unit)⁻¹ : Branch c i) * x)
    (ContactBicanonicalCoefficients318.branchQ0_unit c i).unit_spec
  rw [Units.inv_mul] at h
  rw [mul_left_comm,←h,mul_one]

theorem infinity_coefficient_relation :
    ContactBicanonicalCoefficients318.infinityQ0 c=
      reciprocalCoordinate c * ContactBicanonicalCoefficients318.infinityQ1 c := by
  have h : (ContactBicanonicalCoefficients318.infinityScale c 5 : ℚ) =
      (↑((c 0)⁻¹) : ℚ) * (ContactBicanonicalCoefficients318.infinityScale c 4 : ℚ) := by
    simp only [ContactBicanonicalCoefficients318.infinityScale,Units.val_mul,
      Units.val_pow_eq_pow_val,pow_succ]
    ring
  simp only [ContactBicanonicalCoefficients318.infinityQ0,
    ContactBicanonicalCoefficients318.infinityQ1,reciprocalCoordinate,h,map_mul]
  ring

theorem infinityRatio_eq : infinityRatio c=reciprocalCoordinate c := by
  unfold infinityRatio
  have h := congrArg (fun x : Infinity c =>
    (↑((ContactBicanonicalCoefficients318.infinityQ1_unit c).unit)⁻¹ : Infinity c) * x)
    (ContactBicanonicalCoefficients318.infinityQ1_unit c).unit_spec
  rw [Units.inv_mul] at h
  rw [infinity_coefficient_relation,mul_left_comm,←h,mul_one]

/-- The reciprocal ratio is the literal reciprocal projective-base coordinate
under the already checked ramified infinity chart, on its whole ring. -/
theorem reciprocalCoordinate_base :
    ReciprocalInfinityBase318.chartMap c
      (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen c) X)=
        reciprocalCoordinate c := by
  unfold ReciprocalInfinityBase318.chartMap ReciprocalInfinityBase318.openMap
  simp only [RingHom.comp_apply,IsLocalization.Away.map,IsLocalization.map_eq]
  rw [ReciprocalInfinityBase318.substitution_X]
  simp only [map_mul,map_pow]
  unfold reciprocalCoordinate ContactFrameNormalization318.infinityCoordinate
  congr 1
end ContactBicanonicalRatios318
