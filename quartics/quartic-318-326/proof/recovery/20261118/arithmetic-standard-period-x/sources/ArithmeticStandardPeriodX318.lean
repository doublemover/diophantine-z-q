module
public import StandardPeriodAnalytic318
public import UniformTranscendentalPrimitiveEquation318
public import OpenJScalingAmbiguity318
public import MarkedPeriod318
public section
noncomputable section
namespace ArithmeticStandardPeriodX318
open OpenJComplexEvaluation318 OpenJAnalyticPoints318 LatticeInvariants318
open UniformTranscendentalPrimitiveEquation318 MarkedPeriod318
variable (N:ℕ) [NeZero N] (τ:UpperHalfPlane) (h:Admissible τ)

private theorem coefficient_id :
    ModularForm.E₆ τ = (scaling N τ h:ℂ)^2*(12*ModularForm.E₄ τ) ∧
      ModularForm.E₆ τ≠0 := by
  obtain ⟨h4,h6⟩ := scaling_spec N τ h
  have hA : (fiber N τ h).a₄= -3*ActualQJ318.jInvariant τ*(ActualQJ318.jInvariant τ-1728)⁻¹ := by
    rw [fiber_eq];rfl
  have hB : (fiber N τ h).a₆= -2*ActualQJ318.jInvariant τ*(ActualQJ318.jInvariant τ-1728)⁻¹ := by
    rw [fiber_eq];rfl
  change -ModularForm.E₄ τ / 48=(scaling N τ h:ℂ)^4*(fiber N τ h).a₄ at h4
  change -ModularForm.E₆ τ / 864=(scaling N τ h:ℂ)^6*(fiber N τ h).a₆ at h6
  constructor
  · rw [hA] at h4
    rw [hB] at h6
    linear_combination (-864)*h6 + 576*(scaling N τ h:ℂ)^2*h4
  · intro hz
    rw [hz] at h6
    have ht := mul_ne_zero (pow_ne_zero 6 (scaling N τ h).ne_zero)
      (OpenJScalingAmbiguity318.fiber_a6_ne_zero N τ h)
    apply ht
    simpa using h6.symm

/-- For arbitrary analytic points, normalized x and arithmetic x agree
after multiplying by 12 E4/E6. This uses the actual two short coefficients,
not a chosen square root of a modular function. -/
theorem inverse_x (P:(ModularWeierstrass318.curve τ).toAffine.Point) :
    valueX ((pointAddEquiv N τ h).symm P)=
      (12*ModularForm.E₄ τ / ModularForm.E₆ τ)*valueX P := by
  have ⟨h6,hn⟩ := coefficient_id N τ h
  have hu : (scaling N τ h:ℂ)≠0 := (scaling N τ h).ne_zero
  have hs : ((scaling N τ h:ℂ)^2)⁻¹=12*ModularForm.E₄ τ / ModularForm.E₆ τ := by
    apply (eq_div_iff hn).mpr
    rw [h6]
    field_simp
  cases P with
  | zero => simp [pointAddEquiv,ShortScaling318.pointAddEquiv,ShortScaling318.pointEquiv,
      ShortScaling318.pointInverse,valueX]
  | some a b hp =>
    change a/(scaling N τ h:ℂ)^2=12*ModularForm.E₄ τ/ModularForm.E₆ τ*a
    rw [div_eq_mul_inv,hs,mul_comm]

/-- The actual standard arithmetic x-value, in the (0,1) period convention. -/
theorem standard (hN:1<N) :
    valueX ((pointAddEquiv N τ h).symm (standardPoint N τ)) =
      (12*ModularForm.E₄ τ / ModularForm.E₆ τ)*xCoord τ (1/(N:ℂ)) := by
  rw [inverse_x,standardPoint_formula]
  have hz : (N:ℂ)⁻¹∉(PeriodEisenstein318.periods τ).lattice := by
    intro hmem
    have hd := ((EllipticTorsion318.divided_period_mem_iff τ N 0 1).mp
      (by simpa [one_div] using hmem)).2
    have hn : N ∣ 1 := by exact_mod_cast hd
    have := Nat.eq_one_of_dvd_one hn
    omega
  rw [LatticeModelPoint318.point_of_notMem τ _ hz]
  simp [LatticeModelPoint318.affinePoint,valueX,one_div]

end ArithmeticStandardPeriodX318
