module
public import WeierstrassPairInjective318
public import TorusPointInterface318
public section
noncomputable section
namespace TorusInjective318
open PeriodEisenstein318 LatticeInvariants318 ModularWeierstrass318 LatticeModelPoint318
set_option maxHeartbeats 0

/-- The actual elliptic point values are equal exactly at lattice-congruent arguments. -/
theorem point_eq_iff_sub_mem (tau : UpperHalfPlane) (z w : ℂ) :
    point tau z = point tau w ↔ w-z ∈ (periods tau).lattice := by
  constructor
  · intro he
    by_cases hz : z ∈ (periods tau).lattice
    · have hw : w ∈ (periods tau).lattice := by
        apply (TorusPointInterface318.point_eq_zero_iff tau w).mp
        rw [← he]
        exact point_of_mem tau z hz
      exact sub_mem hw hz
    · have hw : w ∉ (periods tau).lattice := by
        intro hw
        apply hz
        apply (TorusPointInterface318.point_eq_zero_iff tau z).mp
        rw [he]
        exact point_of_mem tau w hw
      rw [point_of_notMem tau z hz, point_of_notMem tau w hw] at he
      have hxy := WeierstrassCurve.Affine.Point.some.inj he
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hx : (periods tau).weierstrassP z = (periods tau).weierstrassP w := by
        exact (div_left_inj' (pow_ne_zero 2 (mul_ne_zero (by norm_num) hpi))).mp hxy.1
      have hy : (periods tau).derivWeierstrassP z = (periods tau).derivWeierstrassP w := by
        exact (div_left_inj' (mul_ne_zero (by norm_num)
          (pow_ne_zero 3 (mul_ne_zero (by norm_num) hpi)))).mp hxy.2
      exact (WeierstrassPairInjective318.pair_eq_iff_sub_mem (periods tau) z w hz hw).mp ⟨hx,hy⟩
  · intro h
    have he := point_add_period tau z ⟨w-z,h⟩
    simpa using he.symm

/-- The constructed map from the actual period quotient to the actual elliptic curve is injective.
Surjectivity and compatibility with addition are separate assertions. -/
theorem torusPoint_injective (tau : UpperHalfPlane) : Function.Injective (torusPoint tau) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h z =>
    induction r using Quotient.inductionOn with
    | h w =>
      intro he
      apply Quotient.sound
      apply QuotientAddGroup.leftRel_apply.mpr
      have hm := (point_eq_iff_sub_mem tau z w).mp he
      change -z+w ∈ (periods tau).lattice
      simpa only [sub_eq_add_neg, add_comm] using hm

end TorusInjective318
