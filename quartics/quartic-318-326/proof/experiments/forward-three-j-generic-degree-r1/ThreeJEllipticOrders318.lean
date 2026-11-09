module
public import ActualThreeJQDiscGerms318
public section
noncomputable section
open Filter Topology
namespace ThreeJEllipticOrders318
open ThreeCompactParameter318 ThreeParameterCompositionOrder318 ThreeJAnalyticGerms318
set_option maxHeartbeats 600000

lemma analytic_unit_order {f : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t) (h : f t ≠ 0) :
    meromorphicOrderAt f t=0 := by
  rw [hf.meromorphicOrderAt_eq,hf.analyticOrderAt_eq_zero.mpr h]
  rfl

lemma linear_zero_order (a : ℂ) : meromorphicOrderAt (fun t : ℂ => t+a) (-a)=1 := by
  have h : AnalyticAt ℂ (fun t : ℂ => t+a) (-a) := analyticAt_id.add analyticAt_const
  rw [h.meromorphicOrderAt_eq,
    h.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by simp)]
  rfl

lemma J_analytic {t : ℂ} (ht : t ≠ 0) : AnalyticAt ℂ J t :=
  (finiteN_analytic t).div (analyticAt_id.pow 3) (pow_ne_zero 3 ht)

/-- The simple preimage of zero is retained; it is not incorrectly included
among the ramified points merely because its target is elliptic. -/
theorem order_at_neg27 : meromorphicOrderAt J (-27)=1 := by
  have hid : MeromorphicAt (fun t : ℂ => t) (-27) :=
    (show AnalyticAt ℂ (fun t : ℂ => t) (-27) from analyticAt_id).meromorphicAt
  have hi : meromorphicOrderAt (fun t : ℂ => t) (-27)=0 :=
    analytic_unit_order analyticAt_id (by norm_num)
  have h243 : meromorphicOrderAt (fun t : ℂ => t+243) (-27)=0 :=
    analytic_unit_order (analyticAt_id.add analyticAt_const) (by norm_num)
  have h := J_comp_order hid
  change meromorphicOrderAt J (-27)=_ at h
  rw [linear_zero_order 27,h243,hi] at h
  simpa using h

/-- The other preimage of zero has ramification order three. -/
theorem order_at_neg243 : meromorphicOrderAt J (-243)=3 := by
  have hid : MeromorphicAt (fun t : ℂ => t) (-243) :=
    (show AnalyticAt ℂ (fun t : ℂ => t) (-243) from analyticAt_id).meromorphicAt
  have hi : meromorphicOrderAt (fun t : ℂ => t) (-243)=0 :=
    analytic_unit_order analyticAt_id (by norm_num)
  have h27 : meromorphicOrderAt (fun t : ℂ => t+27) (-243)=0 :=
    analytic_unit_order (analyticAt_id.add analyticAt_const) (by norm_num)
  have h := J_comp_order hid
  change meromorphicOrderAt J (-243)=_ at h
  rw [h27,linear_zero_order 243,hi] at h
  simpa using h

lemma D_analytic (t : ℂ) : AnalyticAt ℂ D t :=
  ((analyticAt_id.pow 2).sub (analyticAt_const.mul analyticAt_id)).sub analyticAt_const

lemma D_deriv (t : ℂ) : deriv D t=2*t-486 := by
  have h : HasDerivAt D (2*t-486) t := by
    simpa only [D,Pi.pow_apply,Pi.sub_apply,Pi.mul_apply,Nat.cast_ofNat,
      pow_one,mul_one,zero_mul,zero_add,mul_zero,sub_zero] using
      (((hasDerivAt_id t).pow 2).sub
        ((hasDerivAt_const t (486:ℂ)).mul (hasDerivAt_id t))).sub_const (19683:ℂ)
  exact h.deriv

lemma root_ne_zero {t : ℂ} (ht : D t=0) : t ≠ 0 := by
  intro h
  subst t
  norm_num [D] at ht

lemma root_deriv_ne_zero {t : ℂ} (ht : D t=0) : deriv D t ≠ 0 := by
  rw [D_deriv]
  intro h
  have he : t=243 := by linear_combination h/2
  rw [he] at ht
  norm_num [D] at ht

lemma D_root_order {t : ℂ} (ht : D t=0) : meromorphicOrderAt D t=1 := by
  rw [(D_analytic t).meromorphicOrderAt_eq,
    (D_analytic t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ht (root_deriv_ne_zero ht)]
  rfl

/-- Every finite preimage described by the exact elliptic quadratic is simple
for that quadratic and has order two for the centered j expression. -/
theorem order_over_1728 {t : ℂ} (ht : D t=0) :
    meromorphicOrderAt (fun z => J z-1728) t=2 := by
  have hn := root_ne_zero ht
  have hid : MeromorphicAt (fun z : ℂ => z) t :=
    (show AnalyticAt ℂ (fun z : ℂ => z) t from analyticAt_id).meromorphicAt
  have hi : meromorphicOrderAt (fun z : ℂ => z) t=0 := analytic_unit_order analyticAt_id hn
  have he : (fun z => J z-1728) =ᶠ[𝓝 t] (fun z => (D z)^2/z^3) := by
    filter_upwards [eventually_ne_nhds hn] with z hz
    exact J_sub_1728 z hz
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  change meromorphicOrderAt (D^2/(fun z : ℂ => z)^3) t=2
  rw [meromorphicOrderAt_div ((D_analytic t).meromorphicAt.pow 2) (hid.pow 3),
    meromorphicOrderAt_pow (D_analytic t).meromorphicAt,meromorphicOrderAt_pow hid,
    D_root_order ht,hi]
  norm_num

lemma zero_fiber {t : ℂ} (ht : t ≠ 0) : J t=0 ↔ t= -27 ∨ t= -243 := by
  unfold J
  rw [div_eq_zero_iff]
  simp only [pow_ne_zero 3 ht,or_false,mul_eq_zero,pow_eq_zero_iff (by decide : 3 ≠ 0),
    add_eq_zero_iff_eq_neg]

lemma elliptic_fiber {t : ℂ} (ht : t ≠ 0) : J t=1728 ↔ D t=0 := by
  rw [←sub_eq_zero,J_sub_1728 t ht,div_eq_zero_iff]
  simp only [pow_ne_zero 3 ht,or_false,pow_eq_zero_iff (by decide : 2 ≠ 0)]

end ThreeJEllipticOrders318
