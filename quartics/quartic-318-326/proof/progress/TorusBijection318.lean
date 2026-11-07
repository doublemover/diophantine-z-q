module
public import WeierstrassSurjective318
public section
noncomputable section
namespace TorusBijection318
open PeriodEisenstein318 LatticeInvariants318 ModularWeierstrass318 LatticeModelPoint318
set_option maxHeartbeats 0

lemma exists_xCoord (tau : UpperHalfPlane) (x : ℂ) :
    ∃ z : ℂ, z ∉ (periods tau).lattice ∧ xCoord tau z = x := by
  obtain ⟨z,hz,he⟩ := WeierstrassSurjective318.exists_value (periods tau) ((2*(Real.pi:ℂ))^2*x)
  refine ⟨z,hz,?_⟩
  rw [xCoord,he]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Every actual point of the normalized complex elliptic curve is obtained from ℘ and ℘'. -/
theorem point_surjective (tau : UpperHalfPlane) : Function.Surjective (point tau) := by
  intro P
  cases P with
  | zero => exact ⟨0,point_of_mem tau 0 (periods tau).lattice.zero_mem⟩
  | some x y hn =>
    obtain ⟨z,hz,hx⟩ := exists_xCoord tau x
    have hy2 := normalized_weierstrass_equation tau z hz
    rw [hx] at hy2
    have he := ((WeierstrassCurve.Affine.nonsingular_iff x y).mp hn).1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    have hey : y^2 = x^3-ModularForm.E₄ tau/48*x-ModularForm.E₆ tau/864 := by
      simpa [curve, NormalizedWeierstrass318.model, sub_eq_add_neg, neg_div, mul_assoc] using he
    have hysq : yCoord tau z ^ 2 = y^2 := hy2.trans hey.symm
    rcases eq_or_eq_neg_of_sq_eq_sq (yCoord tau z) y hysq with hy | hy
    · refine ⟨z,?_⟩
      rw [point_of_notMem tau z hz]
      simp only [affinePoint, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx,hy⟩
    · have hnz : -z ∉ (periods tau).lattice := fun h => hz (neg_mem_iff.mp h)
      refine ⟨-z,?_⟩
      rw [point_of_notMem tau (-z) hnz]
      simp only [affinePoint, WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · simpa only [xCoord,PeriodPair.weierstrassP_neg] using hx
      · have hneg : yCoord tau (-z) = -yCoord tau z := by
          simp only [yCoord, PeriodPair.derivWeierstrassP_neg, neg_div]
        rw [hneg,hy,neg_neg]

/-- The actual period-quotient map is surjective. -/
theorem torusPoint_surjective (tau : UpperHalfPlane) : Function.Surjective (torusPoint tau) := by
  intro P
  obtain ⟨z,hz⟩ := point_surjective tau P
  exact ⟨QuotientAddGroup.mk z,hz⟩

/-- Actual set-level bijectivity; compatibility with addition remains a separate theorem. -/
theorem torusPoint_bijective (tau : UpperHalfPlane) : Function.Bijective (torusPoint tau) :=
  ⟨TorusInjective318.torusPoint_injective tau,torusPoint_surjective tau⟩

/-- The genuine period quotient and normalized elliptic points are in bijection.
This is an equivalence of types, not an AddEquiv or an analytic equivalence. -/
@[expose] def torusEquiv (tau : UpperHalfPlane) :
    (ℂ ⧸ (periods tau).lattice.toAddSubgroup) ≃ (curve tau).toAffine.Point :=
  Equiv.ofBijective (torusPoint tau) (torusPoint_bijective tau)

lemma torusEquiv_apply (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) : torusEquiv tau q = torusPoint tau q := rfl

end TorusBijection318
