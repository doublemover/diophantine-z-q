module
public import ActualTwoDescentHalfFlipOrdinates318
public section
noncomputable section
namespace ActualTwoDescentHalfFlipTranslations318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentHalvingCoordinates318
open ActualTwoDescentGeneralRootTranslation318 ActualTwoDescentHalfFlipProducts318
open ActualTwoDescentHalfFlipOrdinates318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def rootHalf (n x a b c : K) (hn : n ≠ 0) (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) : Point n :=
  point n (halfX x a b c) (halfY a b c) hn (half_curve n x a b c ha hb hc)

lemma actual_root_half_avoids (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfX x a b c ≠ 0 ∧ halfX x a b c-n ≠ 0 ∧ halfX x a b c+3*n ≠ 0 := by
  obtain ⟨hab,hac,hbc⟩ := half_sum_nonzero n x a b c hn ha hb hc
  refine ⟨?_,?_,?_⟩
  · rw [(half_factors n x a b c ha hb hc).1]; exact mul_ne_zero hab hac
  · rw [(half_factors n x a b c ha hb hc).2.1]; exact mul_ne_zero hab hbc
  · rw [(half_factors n x a b c ha hb hc).2.2]; exact mul_ne_zero hac hbc

/-- Flipping the two roots away from0 is exactly translation by(0,0). -/
theorem actual_flip_zero_is_translation (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    rootHalf n x a b c hn ha hb hc+zeroTorsion n hn=
      rootHalf n x a (-b) (-c) hn ha (by simpa using hb) (by simpa using hc) := by
  have hd := (actual_root_half_avoids n x a b c hn ha hb hc).1
  apply actual_add_root_point n _ _ 0 _ _ hn (by simpa only [sub_zero] using hd)
    (half_curve n x a b c ha hb hc) (by ring)
    (half_curve n x a (-b) (-c) ha (by simpa using hb) (by simpa using hc))
  · simp only [rootDerivative,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_add,add_zero,zero_sub,sub_zero]
    apply (eq_div_iff hd).mpr
    have h := actual_half_flip_zero_product n x a b c ha hb hc
    linear_combination h
  · apply (eq_div_iff (pow_ne_zero 2 (by simpa only [sub_zero] using hd))).mpr
    have h := actual_half_flip_zero_ordinate n x a b c ha hb hc
    dsimp [rootDerivative]
    linear_combination h

/-- Flipping the roots away from n is exactly translation by(n,0). -/
theorem actual_flip_first_is_translation (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    rootHalf n x a b c hn ha hb hc+firstTorsion n hn=
      rootHalf n x (-a) b (-c) hn (by simpa using ha) hb (by simpa using hc) := by
  have hd := (actual_root_half_avoids n x a b c hn ha hb hc).2.1
  apply actual_add_root_point n _ _ n _ _ hn hd (half_curve n x a b c ha hb hc) (by ring)
    (half_curve n x (-a) b (-c) (by simpa using ha) hb (by simpa using hc))
  · have hquot : halfX x (-a) b (-c)-n=rootDerivative n n/(halfX x a b c-n) := by
      apply (eq_div_iff hd).mpr
      have h := actual_half_flip_first_product n x a b c ha hb hc
      dsimp [rootDerivative]
      linear_combination h
    linear_combination hquot
  · apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
    have h := actual_half_flip_first_ordinate n x a b c ha hb hc
    dsimp [rootDerivative]
    linear_combination h

/-- Flipping the roots away from -3n is exactly translation by(-3n,0). -/
theorem actual_flip_last_is_translation (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    rootHalf n x a b c hn ha hb hc+torsionPoint n hn=
      rootHalf n x (-a) (-b) c hn (by simpa using ha) (by simpa using hb) hc := by
  have hd : halfX x a b c-(-3*n) ≠ 0 := by
    simpa only [sub_neg_eq_add] using (actual_root_half_avoids n x a b c hn ha hb hc).2.2
  apply actual_add_root_point n _ _ (-3*n) _ _ hn hd (half_curve n x a b c ha hb hc) (by ring)
    (half_curve n x (-a) (-b) c (by simpa using ha) (by simpa using hb) hc)
  · have hquot : halfX x (-a) (-b) c+3*n=rootDerivative n (-3*n)/(halfX x a b c-(-3*n)) := by
      apply (eq_div_iff hd).mpr
      have h := actual_half_flip_last_product n x a b c ha hb hc
      dsimp [rootDerivative]
      linear_combination h
    linear_combination hquot
  · apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
    have h := actual_half_flip_last_ordinate n x a b c ha hb hc
    dsimp [rootDerivative]
    linear_combination h

end ActualTwoDescentHalfFlipTranslations318
