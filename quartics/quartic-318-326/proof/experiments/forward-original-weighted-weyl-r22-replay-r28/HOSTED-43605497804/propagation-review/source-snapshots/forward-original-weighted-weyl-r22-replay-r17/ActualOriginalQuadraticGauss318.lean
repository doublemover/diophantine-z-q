module
public import ActualOriginalZeroModeLimit318
public section
noncomputable section
namespace ActualOriginalQuadraticGauss318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def quadraticGauss (q : ℕ) [NeZero q] (c b : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (c*x^2+b*x)

lemma actual_standard_character_star (q : ℕ) [NeZero q] (x : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change starRingEnd ℂ (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

lemma actual_standard_character_norm (q : ℕ) [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := Circle.norm_coe _

/-- Exact quadratic differencing over EVERY nonzero modulus, including
composite and even q. Degeneracy is the actual multiplication kernel2*c,
not a field-only cancellation assumption. -/
theorem actual_quadratic_gauss_correlation (q : ℕ) [NeZero q] (c b : ZMod q) :
    quadraticGauss q c b * starRingEnd ℂ (quadraticGauss q c b) =
      (q : ℂ) * ∑ h : ZMod q,
        if 2*c*h=0 then ZMod.stdAddChar (c*h^2+b*h) else 0 := by
  classical
  have hr (y : ZMod q) :
      (∑ x : ZMod q, ZMod.stdAddChar ((c*x^2+b*x)-(c*y^2+b*y))) =
        ∑ h : ZMod q, ZMod.stdAddChar ((c*(h+y)^2+b*(h+y))-(c*y^2+b*y)) :=
    (Equiv.sum_comp (Equiv.addRight y)
      (fun x : ZMod q => ZMod.stdAddChar ((c*x^2+b*x)-(c*y^2+b*y)))).symm
  calc
    quadraticGauss q c b * starRingEnd ℂ (quadraticGauss q c b) =
        ∑ y : ZMod q, ∑ x : ZMod q,
          ZMod.stdAddChar ((c*x^2+b*x)-(c*y^2+b*y)) := by
      simp only [quadraticGauss,map_sum,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      rw [actual_standard_character_star,←AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ h : ZMod q, ∑ y : ZMod q,
        ZMod.stdAddChar (c*h^2+b*h) * ZMod.stdAddChar (y*(2*c*h)) := by
      simp_rw [hr]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro y hy
      rw [←AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ h : ZMod q, ZMod.stdAddChar (c*h^2+b*h) *
        (if 2*c*h=0 then (q : ℂ) else 0) := by
      simp_rw [←Finset.mul_sum,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q),ZMod.card]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      split_ifs <;> simp [mul_comm]

@[expose] def kernelCard (q : ℕ) [NeZero q] (d : ZMod q) : ℕ := by
  classical
  exact (Finset.univ.filter (fun h : ZMod q => d*h=0)).card

/-- Uniform in the arbitrary linear frequency b. This is an actual
quadratic Gauss estimate in terms of the produced degeneracy kernel. -/
theorem actual_quadratic_gauss_square_bound (q : ℕ) [NeZero q] (c b : ZMod q) :
    ‖quadraticGauss q c b‖^2 ≤ (q : ℝ) * kernelCard q (2*c) := by
  classical
  have hk : ‖∑ h : ZMod q, if 2*c*h=0 then ZMod.stdAddChar (c*h^2+b*h) else 0‖ ≤
      (kernelCard q (2*c) : ℝ) := by
    calc
      _ ≤ ∑ h : ZMod q, ‖if 2*c*h=0 then ZMod.stdAddChar (c*h^2+b*h) else 0‖ :=
        norm_sum_le _ _
      _ = _ := by simp [kernelCard,actual_standard_character_norm]
  calc
    ‖quadraticGauss q c b‖^2 =
        ‖quadraticGauss q c b * starRingEnd ℂ (quadraticGauss q c b)‖ := by
      simp [norm_mul,pow_two]
    _ = (q : ℝ) * ‖∑ h : ZMod q,
        if 2*c*h=0 then ZMod.stdAddChar (c*h^2+b*h) else 0‖ := by
      rw [actual_quadratic_gauss_correlation,norm_mul]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg q)

end ActualOriginalQuadraticGauss318
