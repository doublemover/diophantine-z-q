module
public import ActualThreeCompactJPoints318
public section
noncomputable section
open Filter Topology
namespace ThreeJAnalyticGerms318
open ThreeProjectiveJCertificates318 Polynomial
set_option maxHeartbeats 600000

@[expose] def finiteN (t : ℂ) : ℂ := (t+27)*(t+243)^3
@[expose] def reciprocalN (s : ℂ) : ℂ := (1+27*s)*(1+243*s)^3
@[expose] def finitePole (t : ℂ) : ℂ := t^3 / finiteN t
@[expose] def reciprocalPole (s : ℂ) : ℂ := s / reciprocalN s

lemma finiteN_analytic (t : ℂ) : AnalyticAt ℂ finiteN t :=
  (analyticAt_id.add analyticAt_const).mul ((analyticAt_id.add analyticAt_const).pow 3)
lemma reciprocalN_analytic (s : ℂ) : AnalyticAt ℂ reciprocalN s :=
  (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).pow 3)

lemma finite_evaluations (t : ℂ) :
    aeval t finiteNumerator=finiteN t ∧ aeval t finiteDenominator=t^3 := by
  simp [finiteNumerator,finiteDenominator,finiteN]
lemma reciprocal_evaluations (s : ℂ) :
    aeval s reciprocalNumerator=reciprocalN s ∧ aeval s reciprocalDenominator=s := by
  simp [reciprocalNumerator,reciprocalDenominator,reciprocalN]

lemma finiteN_zero : finiteN 0=(3:ℂ)^18 := by norm_num [finiteN]
lemma reciprocalN_zero : reciprocalN 0=1 := by norm_num [reciprocalN]
lemma finiteN_zero_ne : finiteN 0 ≠ 0 := by rw [finiteN_zero]; norm_num
lemma reciprocalN_zero_ne : reciprocalN 0 ≠ 0 := by rw [reciprocalN_zero]; exact one_ne_zero

lemma finitePole_analytic {t : ℂ} (ht : finiteN t ≠ 0) : AnalyticAt ℂ finitePole t :=
  (analyticAt_id.pow 3).div (finiteN_analytic t) ht
lemma reciprocalPole_analytic {s : ℂ} (hs : reciprocalN s ≠ 0) :
    AnalyticAt ℂ reciprocalPole s :=
  analyticAt_id.div (reciprocalN_analytic s) hs

lemma id_order : meromorphicOrderAt (fun t : ℂ => t) 0=1 := by
  have h : AnalyticAt ℂ (fun t : ℂ => t) 0 := analyticAt_id
  rw [h.meromorphicOrderAt_eq,
    h.analyticOrderAt_eq_one_of_zero_deriv_ne_zero rfl (by simp)]
  rfl

lemma finiteN_order : meromorphicOrderAt finiteN 0=0 := by
  rw [(finiteN_analytic 0).meromorphicOrderAt_eq,
    (finiteN_analytic 0).analyticOrderAt_eq_zero.mpr finiteN_zero_ne]
  rfl
lemma reciprocalN_order : meromorphicOrderAt reciprocalN 0=0 := by
  rw [(reciprocalN_analytic 0).meromorphicOrderAt_eq,
    (reciprocalN_analytic 0).analyticOrderAt_eq_zero.mpr reciprocalN_zero_ne]
  rfl

/-- Order of the actual reciprocal target coordinate at the finite source
origin. Analyticity and the zero value exclude a totalization artifact. -/
theorem finite_cusp_germ : AnalyticAt ℂ finitePole 0 ∧ finitePole 0=0 ∧
    meromorphicOrderAt finitePole 0=3 := by
  refine ⟨finitePole_analytic finiteN_zero_ne,by simp [finitePole],?_⟩
  have hid : MeromorphicAt (fun t : ℂ => t) 0 :=
    (show AnalyticAt ℂ (fun t : ℂ => t) 0 from analyticAt_id).meromorphicAt
  change meromorphicOrderAt ((fun t : ℂ => t)^3 / finiteN) 0=3
  rw [meromorphicOrderAt_div (hid.pow 3)
    (finiteN_analytic 0).meromorphicAt,
    meromorphicOrderAt_pow hid,
    id_order,finiteN_order]
  norm_num

/-- At the reciprocal source origin, the same target reciprocal coordinate
has a simple zero, so the two source cusps have different local orders. -/
theorem reciprocal_cusp_germ : AnalyticAt ℂ reciprocalPole 0 ∧ reciprocalPole 0=0 ∧
    meromorphicOrderAt reciprocalPole 0=1 := by
  refine ⟨reciprocalPole_analytic reciprocalN_zero_ne,by simp [reciprocalPole],?_⟩
  have hid : MeromorphicAt (fun t : ℂ => t) 0 :=
    (show AnalyticAt ℂ (fun t : ℂ => t) 0 from analyticAt_id).meromorphicAt
  change meromorphicOrderAt ((fun t : ℂ => t) / reciprocalN) 0=1
  rw [meromorphicOrderAt_div hid
    (reciprocalN_analytic 0).meromorphicAt,id_order,reciprocalN_order,sub_zero]

/-- Explicit finite branch factorization above the classical elliptic value.
This algebraic identity alone does not assert a full ramification divisor. -/
lemma numerator_minus_1728 (t : ℂ) :
    finiteN t-1728*t^3=(t^2-486*t-19683)^2 := by unfold finiteN; ring

end ThreeJAnalyticGerms318
