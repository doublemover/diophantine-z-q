module
public import ActualSourceRatioParameters318
public import JLinear318
public section
noncomputable section
namespace ActualMixedLogPrecision318
open ActualLogHom318 ActualLogIdentification318 ActualLogRatio318 CanonicalRoot318
open ConcreteG8Domain ConcretePadic318 CoherentMultipleCharts318 ActualOrientedLogMembership318
open ActualReciprocalParameters318 ValuativeOrbitBounds318 Pade21Domains
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

lemma factor_J (hp : 19≤p) (D u v : ℚ_[p]) (hc : v^2=1-D*u^4)
    (hw : ‖D*u^4‖<1) (hv : ‖v-1‖<1) :
    factor p hp (D*u^4)=v*JTail318.J p (v-1) := by
  have hroot := root_unique p hp (D*u^4) _ v (root_spec p hp _ hw).1 hc
    (root_spec p hp _ hw).2 hv
  have he : D*u^4= -2*(v-1)-(v-1)^2 := by linear_combination hc
  simp only [factor,GTail318.G,hroot,JTail318.J,he]

/-- Relative J errors are proved on the actual positive ordinate, not on an
independently selected square root. -/
lemma factor_J_errors (hp : 19≤p) (D u v : ℚ_[p]) (hu : u≠0)
    (hD : Padic.addValuation D=0) (hc : v^2=1-D*u^4)
    (hn : Near Padic.addValuation 1 u v) :
    Bound Padic.addValuation 8 (factor p hp (D*u^4)-v*(1-(v-1)/5)) ∧
    Bound Padic.addValuation 16 (factor p hp (D*u^4)-v*(PJ (v-1)/QJ (v-1))) := by
  let r := u.valuation
  have hr : 1≤r := finite_depth_ge p u hu 1 hn.1
  have hw := argument_depth p D u hD hu
  have hsmall : ‖D*u^4‖<1 := argument_small p _ r hr hw
  have hvsmall : ‖v-1‖<1 := by
    have he := (HTail318.norm_le_iff_valuation p (v-1) 1).mpr hn.2
    have he' : ‖v-1‖≤‖(p:ℚ_[p])‖ := by simpa only [Padic.norm_p,zpow_neg_one] using he
    exact he'.trans_lt (Padic.norm_p_lt_one (p:=p))
  have hroot : root p hp (D*u^4)=v := root_unique p hp _ _ _
    (root_spec p hp _ hsmall).1 hc (root_spec p hp _ hsmall).2 hvsmall
  have hd : (v-1).valuation=4*r := by
    rw [←hroot]
    exact root_depth p hp _ r hr hw
  have hvunit : Padic.addValuation v=0 := one_near_unit _ (by norm_num : (0:ℤ)<1) hn.2
  have hvint : Bound Padic.addValuation 0 v := by rw [Bound,hvunit]
  have h8 := bmul_unit_left Padic.addValuation hvint
    (JLinear318.full_J_linear_precision p hp (v-1) r hr (Or.inr hd))
  have h16 := bmul_unit_left Padic.addValuation hvint
    (SeriesEndpoints318.J_precision_zero_or_finite p hp (v-1) r hr (Or.inr hd))
  rw [factor_J p hp D u v hc hsmall hvsmall]
  constructor
  · convert weaken Padic.addValuation h8 (by omega : 8≤8*r) using 1 <;> ring
  · convert weaken Padic.addValuation h16 (by omega : 16≤16*r) using 1 <;> ring

/-- Combining a J numerator with the original G denominator preserves the
full error precision, because the actual integer logarithm ratio makes the
z-ratio integral. No division-depth premise is hidden in this comparison. -/
lemma mixed_ratio (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) (n N : ℤ) (A B : ℚ_[p])
    (hlog : logHom p hp D hD P/logHom p hp D hD Q=(n:ℚ_[p]))
    (hP : Padic.addValuation (factor p hp (wParameter p D P.val))=0)
    (hQ : Padic.addValuation (factor p hp (wParameter p D Q.val))=0)
    (hB : Padic.addValuation B=0)
    (hA : Bound Padic.addValuation N (factor p hp (wParameter p D P.val)-A))
    (hAB : Bound Padic.addValuation N (factor p hp (wParameter p D Q.val)-B)) :
    Bound Padic.addValuation N ((zParameter p D P.val/zParameter p D Q.val)*(A/B)-(n:ℚ_[p])) := by
  have he := ratio_error Padic.addValuation A B
    (factor p hp (wParameter p D P.val)) (factor p hp (wParameter p D Q.val))
    (N:WithTop ℤ) hB hP hQ
    (by simpa only [neg_sub] using bneg Padic.addValuation hA)
    (by simpa only [neg_sub] using bneg Padic.addValuation hAB)
  have hb := bmul_unit_left Padic.addValuation
    (ActualPrimaryLogPrecision318.z_ratio_integral p hp D hD P Q n hlog) he
  rw [←hlog,log_ratio]
  convert hb using 1 <;> ring

/-- Both alternate rational approximants at the actual integer multiple:
linear J gives depth8; J-Padé gives depth16, with the same original G-Padé
common denominator. The source chooses linear only for its first label. -/
theorem original_ratios (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2)
    (h7 : ¬p∣49) (h n : ℤ) (hzero : h≠0) (hnzero : n≠0)
    (hbase : Near (place p rho hr) 1 (chartU h) (chartV h))
    (hmult : Near (place p rho hr) 1 (chartU (n*h)) (chartV (n*h))) :
    Bound (place p rho hr) 8
      ((-chartU (n*h)*(1-(chartV (n*h)-1)/5))/
        ((-chartU h/chartV h)*(PG (ConcreteG8Domain.D*(chartU h)^4)/
          QG (ConcreteG8Domain.D*(chartU h)^4)))-(n:K)) ∧
    Bound (place p rho hr) 16
      ((-chartU (n*h)*(PJ (chartV (n*h)-1)/QJ (chartV (n*h)-1)))/
        ((-chartU h/chartV h)*(PG (ConcreteG8Domain.D*(chartU h)^4)/
          QG (ConcreteG8Domain.D*(chartU h)^4)))-(n:K)) := by
  let σ := embedding p rho hr
  let Dp := σ ConcreteG8Domain.D
  obtain ⟨Q,hQ,hall⟩ := integer_log_ratios p hp rho hr h hzero hbase
  let P := n • Q
  have hP : P.val=mappedPoint p rho hr (n*h) := (hall n).1
  have hlog : logHom p hp Dp _ P/logHom p hp Dp _ Q=(n:ℚ_[p]) := (hall n).2
  let u := σ (chartU (n*h))
  let v := σ (chartV (n*h))
  let a := σ (chartU h)
  have hu : u≠0 := mapped_u_ne p rho hr _ (mul_ne_zero hnzero hzero)
  have ha : a≠0 := mapped_u_ne p rho hr _ hzero
  have hDp : Padic.addValuation Dp=0 := coefficient_unit p rho hr h7
  have hr1 : 1≤u.valuation := finite_depth_ge p u hu 1 hmult.1
  have hs1 : 1≤a.valuation := finite_depth_ge p a ha 1 hbase.1
  have hwP : wParameter p Dp P.val=Dp*u^4 := by rw [hP,mapped_w,map_mul,map_pow]
  have hwQ : wParameter p Dp Q.val=Dp*a^4 := by rw [hQ,mapped_w,map_mul,map_pow]
  have hpw := argument_depth p Dp u hDp hu
  have hqw := argument_depth p Dp a hDp ha
  have hPu : Padic.addValuation (factor p hp (wParameter p Dp P.val))=0 := by
    rw [hwP]; exact factor_unit p hp _ _ hr1 (Or.inr hpw)
  have hQu : Padic.addValuation (factor p hp (wParameter p Dp Q.val))=0 := by
    rw [hwQ]; exact factor_unit p hp _ _ hs1 (Or.inr hqw)
  have hGu := pade_factor_unit p hp (Dp*a^4) a.valuation hs1 (Or.inr hqw)
  have hG : Bound Padic.addValuation 16
      (factor p hp (wParameter p Dp Q.val)-PG (Dp*a^4)/QG (Dp*a^4)) := by
    rw [hwQ]
    exact weaken _ (factor_pade_precision p hp _ _ hs1 (Or.inr hqw)) (by omega)
  have hc : v^2=1-Dp*u^4 := by
    simpa only [map_pow,map_sub,map_one,map_mul] using congrArg σ (CoherentAdditionV318.chart_curve (n*h))
  have hn : Near Padic.addValuation 1 u v := by
    refine ⟨hmult.1,?_⟩
    have he := hmult.2
    change (1:WithTop ℤ)≤Padic.addValuation (σ (chartV (n*h)-1)) at he
    simpa only [map_sub,map_one] using he
  obtain ⟨h8,h16⟩ := factor_J_errors p hp Dp u v hu hDp hc hn
  rw [←hwP] at h8 h16
  have he8 := mixed_ratio p hp Dp _ P Q n 8 (v*(1-(v-1)/5))
    (PG (Dp*a^4)/QG (Dp*a^4)) hlog hPu hQu hGu h8 (weaken _ hG (by norm_num))
  have he16 := mixed_ratio p hp Dp _ P Q n 16 (v*(PJ (v-1)/QJ (v-1)))
    (PG (Dp*a^4)/QG (Dp*a^4)) hlog hPu hQu hGu h16 hG
  rw [hP,hQ,mapped_z,mapped_z] at he8 he16
  have hv : v≠0 := fun he => CoherentAdditionV318.chartV_ne (n*h)
    (σ.injective (he.trans (map_zero _).symm))
  have hid (b J G : ℚ_[p]) :
      ((-u/v)/b)*(v*J/G)=(-u*J)/(b*G) := by
    rw [div_mul_div_comm]
    congr 1
    field_simp [hv] <;> ring
  simp only [map_div₀,map_neg] at he8 he16
  rw [hid] at he8 he16
  constructor
  · change (8:WithTop ℤ)≤Padic.addValuation (σ _)
    simpa [σ,Dp,u,v,a,map_sub,map_div₀,map_mul,map_pow,PG,QG] using he8
  · change (16:WithTop ℤ)≤Padic.addValuation (σ _)
    simpa [σ,Dp,u,v,a,map_sub,map_div₀,map_mul,map_pow,PG,QG,PJ,QJ] using he16

end ActualMixedLogPrecision318
