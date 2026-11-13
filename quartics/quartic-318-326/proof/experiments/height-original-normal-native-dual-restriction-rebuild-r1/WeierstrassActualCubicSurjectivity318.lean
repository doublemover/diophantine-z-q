module
public import WeierstrassReciprocalPole318
public section
noncomputable section
namespace WeierstrassActualCubicSurjectivity318
open Complex WeierstrassReciprocalPole318
set_option maxHeartbeats 3200000
variable (P : PeriodPair)

/-- Every finite value is attained by the genuine Weierstrass function
OFF its original full lattice. Otherwise its removable reciprocal is
entire and periodic, hence bounded and constant, contradicting its pole value. -/
theorem exists_value (a : ℂ) : ∃ z∉P.lattice,P.weierstrassP z=a := by
  by_contra h
  push_neg at h
  have hd : Differentiable ℂ (reciprocal P a) := fun z =>
    (reciprocal_entire P a h z).differentiableAt
  have hb := IsZLattice.isCompact_range_of_periodic P.lattice (reciprocal P a)
    hd.continuous (fun z l hl => reciprocal_add_period P a z ⟨l,hl⟩)
  have he := hd.apply_eq_apply_of_bounded hb.isBounded (P.ω₁/2) 0
  have hn := P.ω₁_div_two_notMem_lattice
  have hden := sub_ne_zero.mpr (h (P.ω₁/2) hn)
  rw [reciprocal_zero,reciprocal,if_neg hn] at he
  exact (div_ne_zero one_ne_zero hden) he

/-- Every affine point of the ACTUAL lattice-sum cubic is reached by the
original pair (P,Pprime). The opposite representative handles the exact
other square-root sign; no point-surjectivity axiom is supplied. -/
theorem exists_cubic_point (x y : ℂ)
    (hc : y^2=4*x^3-P.g₂*x-P.g₃) :
    ∃ z∉P.lattice,P.weierstrassP z=x ∧ P.derivWeierstrassP z=y := by
  obtain ⟨z,hz,hx⟩ := exists_value P x
  have hp := P.derivWeierstrassP_sq z hz
  rw [hx] at hp
  have hm : (P.derivWeierstrassP z-y)*(P.derivWeierstrassP z+y)=0 := by
    linear_combination hp-hc
  rcases mul_eq_zero.mp hm with h | h
  · exact ⟨z,hz,hx,sub_eq_zero.mp h⟩
  · refine ⟨-z,?_,?_,?_⟩
    · intro hneg
      exact hz (by simpa only [neg_neg] using P.lattice.neg_mem hneg)
    · rw [P.weierstrassP_neg,hx]
    · rw [P.derivWeierstrassP_neg]
      linear_combination -h
end WeierstrassActualCubicSurjectivity318
