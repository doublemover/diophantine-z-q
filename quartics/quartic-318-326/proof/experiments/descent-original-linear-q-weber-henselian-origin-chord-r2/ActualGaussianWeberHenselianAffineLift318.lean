module
public import ActualGaussianWeberHenselianChart318
public section
noncomputable section

namespace ActualGaussianWeberHenselianAffineLift318

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

private theorem same_residue {x y : R} (h : x-y ∈ maximalIdeal R) :
    residue R x=residue R y := by
  have h0 := (residue_eq_zero_iff (x-y)).mpr h
  exact sub_eq_zero.mp (by simpa only [map_sub] using h0)

/-- Every affine point on the literal odd smooth fibre admits an
integral lift, using a monic quadratic when y ≠ 0 and a monic
cubic when y = 0. No simultaneous multi-variable Hensel API is used. -/
theorem affine_lift (h2 : (2:ResidueField R) ≠ 0)
    (x y : ResidueField R) (h : y^2=x^3-x) :
    ∃ a b : R, b^2=a^3-a ∧ residue R a=x ∧ residue R b=y := by
  obtain ⟨a,ha⟩ := (residue_surjective (R:=R)) x
  by_cases hy : y=0
  · have hX : x*(x^2-1)=0 := by rw [hy] at h; linear_combination -h
    have hD : (3:ResidueField R)*x^2-1 ≠ 0 := by
      rcases mul_eq_zero.mp hX with hx | hx
      · simp [hx]
      · have H : x^2=1 := sub_eq_zero.mp hx
        rw [H]
        convert h2 using 1 <;> ring
    let f : R[X] := X^3-X
    have hf : f.Monic := monic_X_pow_sub (by rw [degree_X]; decide)
    have h0 : f.eval a ∈ maximalIdeal R := (residue_eq_zero_iff _).mp (by
      simp only [f,eval_sub,eval_pow,eval_X,map_sub,map_pow,ha]
      rw [hy] at h
      simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using h.symm)
    have h1 : IsUnit (f.derivative.eval a) := (residue_ne_zero_iff_isUnit _).mp (by
      simpa [f,derivative_X_pow,ha] using hD)
    obtain ⟨A,hA,hAa⟩ := HenselianLocalRing.is_henselian f hf a h0 h1
    have hA0 : A^3-A=0 := by simpa [f] using (IsRoot.def.mp hA)
    exact ⟨A,0,by rw [hA0]; simp,(same_residue hAa).trans ha,by simp [hy]⟩
  · obtain ⟨b,hb⟩ := (residue_surjective (R:=R)) y
    let f : R[X] := X^2-C (a^3-a)
    have hf : f.Monic := monic_X_pow_sub_C _ (by decide)
    have h0 : f.eval b ∈ maximalIdeal R := (residue_eq_zero_iff _).mp (by
      simp only [f,eval_sub,eval_pow,eval_X,eval_C,map_sub,map_pow,ha,hb]
      exact sub_eq_zero.mpr h)
    have h1 : IsUnit (f.derivative.eval b) := (residue_ne_zero_iff_isUnit _).mp (by
      simpa [f,derivative_X_pow,hb] using mul_ne_zero h2 hy)
    obtain ⟨B,hB,hBb⟩ := HenselianLocalRing.is_henselian f hf b h0 h1
    have hB0 : B^2=a^3-a := by
      apply sub_eq_zero.mp
      simpa [f] using (IsRoot.def.mp hB)
    exact ⟨a,B,hB0,ha,(same_residue hBb).trans hb⟩

end ActualGaussianWeberHenselianAffineLift318
