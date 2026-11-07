module
public import CMArchimedean318
public section
noncomputable section
open scoped Real
namespace CMIsogeny318
set_option maxHeartbeats 0

 theorem log_fourteen : Real.log (14:ℝ)<3 := by
  have h:=Real.log_lt_log (by norm_num : (0:ℝ)<14) (by norm_num : (14:ℝ)<2^4)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

 theorem log_576 : Real.log (576:ℝ)<7 := by
  have h:=Real.log_lt_log (by norm_num : (0:ℝ)<576) (by norm_num : (576:ℝ)<2^10)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

 theorem log_seven : Real.log (7:ℝ)<2 := by
  have he:Real.exp (2:ℝ)=(Real.exp 1)^2 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add,pow_two]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<7)).mpr
  rw [he]
  nlinarith [Real.exp_one_gt_d9]

@[expose] def base (d h:ℝ) : ℝ := 14^32*d*max 1 (max (Real.log d) h)
@[expose] def Xi (d h:ℝ) : ℝ := (base d h)^8

/-- The exact dimension-two degree expression from GR Theorem1.9(1),
combined with the ordinary half-log degree variation. -/
theorem half_log_degree (d h deg:ℝ) (hd:0<d) (hdeg:0<deg)
    (hbound:deg≤(Xi d h)^2) :
    (1/2)*Real.log deg ≤ 8*(32*Real.log 14+Real.log d+
      Real.log (max 1 (max (Real.log d) h))) := by
  have hm:0<max 1 (max (Real.log d) h):=lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb:0<base d h:=by dsimp [base]; positivity
  have he:=Real.log_le_log hdeg hbound
  unfold Xi at he
  rw [Real.log_pow,Real.log_pow] at he
  unfold base at he
  rw [Real.log_mul (mul_ne_zero (by positivity) hd.ne') hm.ne',
    Real.log_mul (by positivity) hd.ne',Real.log_pow] at he
  norm_num only [Nat.cast_ofNat] at he
  linarith

 theorem max_bound (R d h:ℝ) (hR:1≤R) (hd:0<d) (hdegree:d≤576) (hh:h≤6*R) :
    max 1 (max (Real.log d) h)≤7*R := by
  have hlog:Real.log d<7:=(Real.log_le_log hd hdegree).trans_lt log_576
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

 theorem surface_854 (R d hAprime hA:ℝ) (hR:1≤R) (hd:0<d)
    (hdegree:d≤576) (hprime:hAprime<6*R)
    (hvariation:hA≤hAprime+8*(32*Real.log 14+Real.log d+
      Real.log (max 1 (max (Real.log d) hAprime)))) : hA<854*R := by
  have hRp:0<R:=by linarith
  have hmpos:0<max 1 (max (Real.log d) hAprime):=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm:=Real.log_le_log hmpos (max_bound R d hAprime hR hd hdegree hprime.le)
  rw [Real.log_mul (by norm_num : (7:ℝ)≠0) hRp.ne'] at hm
  have hdlog:Real.log d<7:=(Real.log_le_log hd hdegree).trans_lt log_576
  have hlogR:=Real.log_le_self hRp.le
  linarith [log_fourteen,log_seven]

/-- Complete finite CM-height assembly with the two fields kept distinct:
q is the arbitrary good-reduction extension degree used only in Silverman's
average; d <= 576 is the original same-field isogeny degree parameter. -/
theorem cm_surface_from_periods (q:ℕ) (hq:1≤q) (z:Fin q→ℂ)
    (D R d deg hE hAprime hA:ℝ) (hD:0≤D) (hR:1≤R) (hDR:D≤4*R)
    (hy:∀i,Real.sqrt 3/2≤(z i).im) (hupper:∀i,(z i).im≤Real.sqrt D/2)
    (hSilverman:hE=(∑i,CMArchimedean318.summand (z i))/(q:ℝ))
    (hproduct:hAprime=2*hE) (hd:0<d) (hdegree:d≤576) (hdeg:0<deg)
    (hGR:deg≤(Xi d hAprime)^2) (hvariation:hA≤hAprime+(1/2)*Real.log deg) :
    hA<854*R := by
  have he:hE<3*R:=by
    rw [hSilverman]
    exact CMArchimedean318.average_bound q hq z D R hD hR hDR hy hupper
  have hp:hAprime<6*R:=by rw [hproduct]; linarith
  apply surface_854 R d hAprime hA hR hd hdegree hp
  have hl:=half_log_degree d hAprime deg hd hdeg hGR
  linarith

end CMIsogeny318
#print axioms CMIsogeny318.cm_surface_from_periods
