module
public import ThreeCompactParameter318
public import Mathlib.Analysis.Analytic.Constructions
public section
noncomputable section
open Filter Topology
namespace ThreeExceptionalParameter318
set_option maxHeartbeats 0

@[expose] def relation (a b u : ℂ) : ℂ := 6912*u^4-288*a*u^2-32*b*u-a^2
@[expose] def primaryNumerator (a u : ℂ) : ℂ := 27*(144*u^2-a)
@[expose] def primaryDenominator (a u : ℂ) : ℂ := a-16*u^2
@[expose] def secondaryNumerator (a b u : ℂ) : ℂ := 27*(b+4*a*u+1152*u^3)
@[expose] def secondaryDenominator (b u : ℂ) : ℂ := 64*u^3-b
@[expose] def primary (a u : ℂ) : ℂ := primaryNumerator a u/primaryDenominator a u
@[expose] def secondary (a b u : ℂ) : ℂ := secondaryNumerator a b u/secondaryDenominator b u

lemma cross_multiply (a b u : ℂ) :
    primaryNumerator a u*secondaryDenominator b u-
      secondaryNumerator a b u*primaryDenominator a u=108*u*relation a b u := by
  unfold primaryNumerator primaryDenominator secondaryNumerator secondaryDenominator relation
  ring

lemma denominator_cover {a b u : ℂ} (hd : a^3-b^2 ≠ 0) :
    primaryDenominator a u ≠ 0 ∨ secondaryDenominator b u ≠ 0 := by
  by_cases ha : primaryDenominator a u=0
  · right
    intro hb
    have he4 : a=16*u^2 := sub_eq_zero.mp ha
    have he6 : b=64*u^3 := (sub_eq_zero.mp hb).symm
    apply hd
    rw [he4,he6]
    ring
  · exact Or.inl ha

lemma primary_zero_iff {a b u : ℂ} (hd : a^3-b^2 ≠ 0) (hr : relation a b u=0) :
    primaryDenominator a u=0 ↔ a=0 ∧ u=0 := by
  constructor
  · intro ha
    have he4 : a=16*u^2 := sub_eq_zero.mp ha
    have hh : u*secondaryDenominator b u=0 := by
      unfold relation at hr
      unfold primaryDenominator at ha
      unfold secondaryDenominator
      linear_combination (1/32:ℂ)*hr+(1/32:ℂ)*(a+304*u^2)*ha
    have hb := (denominator_cover hd).resolve_left (not_not.mpr ha)
    have hu := (mul_eq_zero.mp hh).resolve_right hb
    exact ⟨by rw [he4,hu]; ring,hu⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [primaryDenominator]

lemma primary_eq_secondary {a b u : ℂ} (hr : relation a b u=0)
    (ha : primaryDenominator a u ≠ 0) (hb : secondaryDenominator b u ≠ 0) :
    primary a u=secondary a b u := by
  unfold primary secondary
  apply (div_eq_div_iff ha hb).mpr
  have he := cross_multiply a b u
  rw [hr,mul_zero] at he
  exact sub_eq_zero.mp he

/-- Two explicit rational charts, agreeing by the genuine third-division
equation. The choice only supplies a total function, not analyticity by fiat. -/
@[expose] def glued (a b u : ℂ) : ℂ :=
  if primaryDenominator a u=0 then secondary a b u else primary a u

lemma glued_primary {a b u : ℂ} (ha : primaryDenominator a u ≠ 0) :
    glued a b u=primary a u := if_neg ha

lemma glued_secondary {a b u : ℂ} (hr : relation a b u=0)
    (hb : secondaryDenominator b u ≠ 0) : glued a b u=secondary a b u := by
  by_cases ha : primaryDenominator a u=0
  · exact if_pos ha
  · rw [glued_primary ha]
    exact primary_eq_secondary hr ha hb

lemma exceptional_value {b : ℂ} (hb : b ≠ 0) : glued 0 b 0 = -27 := by
  simp [glued,primaryDenominator,secondary,secondaryNumerator,secondaryDenominator]
  field_simp

/-- Actual holomorphic gluing across every point of a nonsingular family.
The relation is consumed throughout the neighborhood, not only at its center. -/
theorem glued_analyticAt {f g h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hd : (f z)^3-(g z)^2 ≠ 0)
    (hr : ∀ᶠ w in 𝓝 z, relation (f w) (g w) (h w)=0) :
    AnalyticAt ℂ (fun w => glued (f w) (g w) (h w)) z := by
  have ha : AnalyticAt ℂ (fun w => primaryDenominator (f w) (h w)) z :=
    hf.sub (analyticAt_const.mul (hh.pow 2))
  have hb : AnalyticAt ℂ (fun w => secondaryDenominator (g w) (h w)) z :=
    (analyticAt_const.mul (hh.pow 3)).sub hg
  rcases denominator_cover hd with hn | hn
  · have hp : AnalyticAt ℂ (fun w => primary (f w) (h w)) z :=
      (analyticAt_const.mul ((analyticAt_const.mul (hh.pow 2)).sub hf)).div ha hn
    apply hp.congr
    filter_upwards [ha.continuousAt.eventually_ne hn] with w hw
    exact (glued_primary hw).symm
  · have hp : AnalyticAt ℂ (fun w => secondary (f w) (g w) (h w)) z :=
      (analyticAt_const.mul ((hg.add ((analyticAt_const.mul hf).mul hh)).add
        (analyticAt_const.mul (hh.pow 3)))).div hb hn
    apply hp.congr
    filter_upwards [hb.continuousAt.eventually_ne hn,hr] with w hw hrw
    exact (glued_secondary hrw hw).symm

/-- Comparison with the previously fixed literal arithmetic j,x parameter.
All scales and denominators are explicit; no new root choice is introduced. -/
lemma old_parameter_eq_primary {a b u d : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hrel : a^3-b^2=1728*d) :
    ThreeCompactParameter318.parameter (a^3/d) (12*a*u/b)=primary a u := by
  have hj : a^3/d-1728=b^2/d := by
    field_simp
    linear_combination hrel
  unfold ThreeCompactParameter318.parameter ThreeCompactParameter318.numerator
    ThreeCompactParameter318.denominator
  rw [hj]
  have hA : b^2/d*(12*a*u/b)^2-a^3/d=a^2*(144*u^2-a)/d := by
    field_simp
    ring
  have hB : 9*(a^3/d)-b^2/d*(12*a*u/b)^2=9*a^2*(a-16*u^2)/d := by
    field_simp
    ring
  rw [hA,hB]
  unfold primary primaryNumerator primaryDenominator at *
  field_simp
  ring

lemma factor_discriminant {a b u : ℂ} (hr : relation a b u=0) :
    (a-16*u^2)*(144*u^2-a)^3=1024*u^2*(a^3-b^2) := by
  unfold relation at hr
  linear_combination (a^2+288*a*u^2-32*b*u-6912*u^4)*hr

lemma zero_root_coefficient {a b : ℂ} (hr : relation a b 0=0) : a=0 := by
  have hh : a^2=0 := by
    simpa [relation] using hr
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hh

lemma glued_ne_zero {a b u : ℂ} (hd : a^3-b^2 ≠ 0) (hr : relation a b u=0) :
    glued a b u ≠ 0 := by
  by_cases hu : u=0
  · subst u
    have ha := zero_root_coefficient hr
    subst a
    have hb : b ≠ 0 := by intro hb; simp [hb] at hd
    rw [exceptional_value hb]
    norm_num
  · have he := factor_discriminant hr
    have hn : (a-16*u^2)*(144*u^2-a)^3 ≠ 0 := by
      rw [he]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) hd
    have hp := (mul_ne_zero_iff.mp hn).1
    have hN : 144*u^2-a ≠ 0 := by
      intro hN
      simp [hN] at hn
    rw [glued_primary hp]
    exact div_ne_zero (mul_ne_zero (by norm_num) hN) hp

lemma J_ratio (n d : ℂ) (hn : n ≠ 0) (hd : d ≠ 0) :
    ThreeCompactParameter318.J (n/d)=(n+27*d)*(n+243*d)^3/(d*n^3) := by
  unfold ThreeCompactParameter318.J
  field_simp

/-- Exact genuine-j relation, including the filled exceptional point. -/
theorem J_glued {a b u : ℂ} (hd : a^3-b^2 ≠ 0) (hr : relation a b u=0) :
    ThreeCompactParameter318.J (glued a b u)=1728*a^3/(a^3-b^2) := by
  by_cases hu : u=0
  · subst u
    have ha := zero_root_coefficient hr
    subst a
    have hb : b ≠ 0 := by intro hb; simp [hb] at hd
    rw [exceptional_value hb]
    norm_num [ThreeCompactParameter318.J]
  · have he := factor_discriminant hr
    have hn : (a-16*u^2)*(144*u^2-a)^3 ≠ 0 := by
      rw [he]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) hd
    have hp := (mul_ne_zero_iff.mp hn).1
    have hN : 144*u^2-a ≠ 0 := by intro hN; simp [hN] at hn
    rw [glued_primary hp]
    have hj : ThreeCompactParameter318.J (primary a u)=
        1769472*u^2*a^3/((a-16*u^2)*(144*u^2-a)^3) := by
      change ThreeCompactParameter318.J (27*(144*u^2-a)/(a-16*u^2))=_
      rw [J_ratio _ _ (mul_ne_zero (by norm_num) hN) hp]
      rw [show 27*(144*u^2-a)+27*(a-16*u^2)=3456*u^2 by ring,
        show 27*(144*u^2-a)+243*(a-16*u^2)=216*a by ring]
      field_simp [hp,hN]
      ring
    rw [hj,he]
    field_simp
    ring

/-- Invariance of the glued coordinate under the exact modular weights. -/
lemma glued_weight_invariant (a b u c : ℂ) (hc : c ≠ 0) :
    glued (c^4*a) (c^6*b) (c^2*u)=glued a b u := by
  have he : primaryDenominator (c^4*a) (c^2*u)=c^4*primaryDenominator a u := by
    unfold primaryDenominator
    ring
  unfold glued
  rw [he]
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 4 ≠ 0),hc,false_or]
  split_ifs
  · unfold secondary secondaryNumerator secondaryDenominator
    have hn : c^6*b+4*(c^4*a)*(c^2*u)+1152*(c^2*u)^3=
        c^6*(b+4*a*u+1152*u^3) := by ring
    have hd : 64*(c^2*u)^3-c^6*b=c^6*(64*u^3-b) := by ring
    rw [hn,hd]
    field_simp
  · unfold primary primaryNumerator primaryDenominator
    have hn : 144*(c^2*u)^2-c^4*a=c^4*(144*u^2-a) := by ring
    have hd : c^4*a-16*(c^2*u)^2=c^4*(a-16*u^2) := by ring
    rw [hn,hd]
    field_simp

end ThreeExceptionalParameter318
