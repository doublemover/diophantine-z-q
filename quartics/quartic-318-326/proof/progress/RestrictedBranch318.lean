module
public import ScaledClosedDisc318
public section
namespace RestrictedBranch318
open PowerSeries RestrictedEvaluation318 ScaledCoefficients318 ScaledDecay318 ScaledFormalSeries318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
variable (p:ℕ) [Fact p.Prime]

 theorem Hscaled_zero (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) : coeff 0 (Hscaled p hp D hD)=1 := by
  apply PadicInt.ext
  simp [coeff_Hscaled,coe_hIntegralCoefficient,hCoefficient,HCoefficients318.coefficient]

/-- Uniform geometric error at every integral argument, including units. -/
 theorem Hscaled_error (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (Hscaled p hp D hD) t-1‖≤‖(p:ℚ_[p])‖^3 := by
  have hs:=Hscaled_summable p hp D hD t
  have hz:=Hscaled_zero p hp D hD
  rw [eval,hs.tsum_eq_zero_add,hz,pow_zero,mul_one]
  rw [add_sub_cancel_left]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  calc
    ‖coeff (n+1) (Hscaled p hp D hD)*t^(n+1)‖≤‖coeff (n+1) (Hscaled p hp D hD)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    _≤(‖(p:ℚ_[p])‖^3)^(n+1) := by
      rw [←PadicInt.norm_coe]
      simp only [coeff_Hscaled,coe_hIntegralCoefficient]
      exact hCoefficient_decay p hp D hD (n+1)
    _≤‖(p:ℚ_[p])‖^3 := by
      simpa using pow_le_pow_of_le_one (pow_nonneg (norm_nonneg (p:ℚ_[p])) 3)
        (ratio_lt_one p 3 (by decide)).le (show 1≤n+1 by omega)

 theorem Hscaled_near_one (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (Hscaled p hp D hD) t-1‖<1 :=
  (Hscaled_error p hp D hD t).trans_lt (ratio_lt_one p 3 (by decide))

 theorem Hscaled_ne_zero (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    eval p (Hscaled p hp D hD) t≠0 := by
  intro he
  have h:=Hscaled_near_one p hp D hD t
  simpa [he] using h

 theorem Bscaled_zero (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) : coeff 0 (Bscaled p hp D hD)=1 := by
  apply PadicInt.ext
  simp [coeff_Bscaled,coe_bIntegralCoefficient,bCoefficient]

/-- Uniform geometric error at every integral argument, including units. -/
 theorem Bscaled_error (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (Bscaled p hp D hD) t-1‖≤‖(p:ℚ_[p])‖^4 := by
  have hs:=Bscaled_summable p hp D hD t
  have hz:=Bscaled_zero p hp D hD
  rw [eval,hs.tsum_eq_zero_add,hz,pow_zero,mul_one]
  rw [add_sub_cancel_left]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  calc
    ‖coeff (n+1) (Bscaled p hp D hD)*t^(n+1)‖≤‖coeff (n+1) (Bscaled p hp D hD)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    _≤(‖(p:ℚ_[p])‖^4)^(n+1) := by
      rw [←PadicInt.norm_coe]
      simp only [coeff_Bscaled,coe_bIntegralCoefficient]
      exact bCoefficient_decay p hp D hD (n+1)
    _≤‖(p:ℚ_[p])‖^4 := by
      simpa using pow_le_pow_of_le_one (pow_nonneg (norm_nonneg (p:ℚ_[p])) 4)
        (ratio_lt_one p 4 (by decide)).le (show 1≤n+1 by omega)

 theorem Bscaled_near_one (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (Bscaled p hp D hD) t-1‖<1 :=
  (Bscaled_error p hp D hD t).trans_lt (ratio_lt_one p 4 (by decide))

 theorem parameter_norm (D:ℚ_[p]) (hD:‖D‖≤1) :
    ‖parameter p D hD‖≤‖(p:ℚ_[p])‖^4 := by
  rw [←PadicInt.norm_coe,coe_parameter,norm_mul,norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hD

/-- The exact evaluated reciprocal ordinate stays on the positive branch,
including scaled unit arguments of original depth one. -/
 theorem branchScaled_error (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (branchScaled p hp D hD) t-1‖≤‖(p:ℚ_[p])‖^4 := by
  rw [ScaledClosedDisc318.eval_branchScaled]
  let B:=eval p (Bscaled p hp D hD) (t^4)
  let a:=parameter p D hD*t^4
  change ‖(1-a)*B-1‖≤_
  have he:(1-a)*B-1=(1-a)*(B-1)-a := by ring
  have ha:‖a‖≤‖(p:ℚ_[p])‖^4 := by
    dsimp [a]
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans
      (parameter_norm p D hD)
  rw [he]
  rw [sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (1-a))).trans
      (Bscaled_error p hp D hD (t^4))
  · simpa only [norm_neg] using ha

 theorem branchScaled_near_one (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    ‖eval p (branchScaled p hp D hD) t-1‖<1 :=
  (branchScaled_error p hp D hD t).trans_lt (ratio_lt_one p 4 (by decide))

 theorem branchScaled_ne_zero (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (t:ℤ_[p]) :
    eval p (branchScaled p hp D hD) t≠0 := by
  intro he
  have h:=branchScaled_near_one p hp D hD t
  simpa [he] using h

end RestrictedBranch318
#print axioms RestrictedBranch318.Bscaled_error
#print axioms RestrictedBranch318.branchScaled_error
#print axioms RestrictedBranch318.branchScaled_near_one

#print axioms RestrictedBranch318.Hscaled_error
#print axioms RestrictedBranch318.Hscaled_near_one
