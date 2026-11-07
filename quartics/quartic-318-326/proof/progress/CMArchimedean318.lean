module
public import CMEta318
public section
noncomputable section
open Finset
open scoped Real
namespace CMArchimedean318
set_option maxHeartbeats 0

/-- The individual archimedean summand in Silverman's original Faltings
normalization after the finite discriminant term vanishes. -/
@[expose] def summand (z:ℂ) : ℝ :=
  -Real.log (2*Real.pi)-Real.log (‖ModularForm.eta z‖^2)-(1/2)*Real.log z.im

 theorem summand_bound (z:ℂ) (D:ℝ) (_hD:0≤D)
    (hy:Real.sqrt 3/2≤z.im) (hupper:z.im≤Real.sqrt D/2) :
    summand z<Real.sqrt D+1 := by
  obtain ⟨hz,_⟩:=CMEta318.reduced_q_bound z hy
  have he:=CMEta318.reduced_eta_bound z hy
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs0:=Real.sqrt_nonneg (3:ℝ)
  have hyhalf:(1:ℝ)/2≤z.im:=by nlinarith
  have hl:=Real.log_le_log (by norm_num : (0:ℝ)<1/2) hyhalf
  rw [one_div,Real.log_inv] at hl
  have hpi:0<Real.log (2*Real.pi):=Real.log_pos (by linarith [Real.pi_gt_three])
  have hyu:=mul_le_mul_of_nonneg_left hupper Real.pi_pos.le
  have hpd:=mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg D)
  dsimp [summand]
  nlinarith [Real.log_two_lt_d9,Real.sqrt_nonneg D]

 theorem sqrt_discriminant_bound (D R:ℝ) (hD:0≤D) (hR:1≤R) (hDR:D≤4*R) :
    Real.sqrt D+1≤3*R := by
  have hs:=Real.sq_sqrt hD
  have hr:=Real.sq_sqrt (show 0≤R by linarith)
  have hs0:=Real.sqrt_nonneg D
  have hr0:=Real.sqrt_nonneg R
  have hsqrt:Real.sqrt D≤2*Real.sqrt R:=by nlinarith
  have hroot:Real.sqrt R≤R:=by nlinarith
  linarith

/-- Actual finite averaging of reduced-period summands. The equality to a
geometric height is not asserted here; it is Silverman's separate input. -/
theorem average_bound (d:ℕ) (hd:1≤d) (z:Fin d→ℂ) (D R:ℝ)
    (hD:0≤D) (hR:1≤R) (hDR:D≤4*R)
    (hy:∀i,Real.sqrt 3/2≤(z i).im) (hupper:∀i,(z i).im≤Real.sqrt D/2) :
    (∑i,summand (z i))/(d:ℝ)<3*R := by
  have hsum:∑i,summand (z i)<∑_:Fin d,3*R := by
    apply sum_lt_sum
    · intro i _
      exact ((summand_bound (z i) D hD (hy i) (hupper i)).trans_le
        (sqrt_discriminant_bound D R hD hR hDR)).le
    · refine ⟨⟨0,by omega⟩,mem_univ _,?_⟩
      exact (summand_bound _ D hD (hy _) (hupper _)).trans_le
        (sqrt_discriminant_bound D R hD hR hDR)
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  apply (div_lt_iff₀ hdR).mpr
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hsum

end CMArchimedean318
#print axioms CMArchimedean318.average_bound
