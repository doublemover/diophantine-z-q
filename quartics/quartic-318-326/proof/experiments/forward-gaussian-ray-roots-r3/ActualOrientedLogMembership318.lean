module
public import SelectedSixComparisonTrace318
public import ActualLogRatio318
public section
noncomputable section
namespace ActualOrientedLogMembership318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open CoherentMultipleCharts318 (chartU chartV)
open ReciprocalDouble318 ShortCurveBaseChange318
open ClosedActualLog318 ActualLogHom318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- An actual positive reciprocal chart of depth1 lies on the SAME analytic
logarithm subgroup. Identity charts are included; no new root is chosen. -/
theorem oriented_mem (hp : 19≤p) (D u v : ℚ_[p]) (hD : ‖D‖≤1)
    (hv : v≠0) (hc : v^2=1-D*u^4)
    (hu : (1:WithTop ℤ)≤Padic.addValuation u)
    (hd : (1:WithTop ℤ)≤Padic.addValuation (v-1)) :
    point D u v hv hc∈formalSubgroup p hp D hD := by
  have hup : ‖u‖≤‖(p:ℚ_[p])‖ := by
    simpa only [Padic.norm_p,zpow_neg_one] using (HTail318.norm_le_iff_valuation p u 1).mpr hu
  have hp0 : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hquot : ‖u/(p:ℚ_[p])‖≤1 := by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp0)).mpr hup
  let t : ℤ_[p] := (u/(p:ℚ_[p])).lift hquot
  have hut : U p t=u := by
    dsimp [U,t]
    field_simp [hp0]
  have hnear : ‖v-1‖<1 := by
    have he := (HTail318.norm_le_iff_valuation p (v-1) 1).mpr hd
    have hn : ‖v-1‖≤‖(p:ℚ_[p])‖ := by simpa only [Padic.norm_p,zpow_neg_one] using he
    exact hn.trans_lt (Padic.norm_p_lt_one (p:=p))
  have hvt : V p hp D hD t=v := by
    apply CanonicalRoot318.root_unique p hp (D*u^4)
    · simpa only [hut] using ClosedActualLog318.curve p hp D hD t
    · exact hc
    · simpa only [V,←PadicInt.coe_one,←PadicInt.coe_sub,PadicInt.norm_coe] using
        ClosedScaledEvaluation318.valueV_near_one p hp D hD t
    · exact hnear
  refine ⟨t,?_⟩
  unfold ClosedActualLog318.chart
  rw [hut,hvt]

@[expose] def mappedPoint (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) :
    (E (embedding p rho hr ConcreteG8Domain.D)).Point :=
  point (embedding p rho hr ConcreteG8Domain.D)
    (embedding p rho hr (chartU n)) (embedding p rho hr (chartV n))
    (fun he => CoherentAdditionV318.chartV_ne n
      ((embedding p rho hr).injective (he.trans (map_zero _).symm)))
    (by simpa only [map_pow,map_sub,map_one,map_mul] using
      congrArg (embedding p rho hr) (CoherentMultipleCharts318.chart_curve n))

lemma mapped_actual (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) :
    mappedPoint p rho hr n=pointMap (embedding p rho hr).toRingHom ConcreteG8Domain.D
      (n • LocalGenerator318.P) := by
  have he := congrArg (pointMap (embedding p rho hr).toRingHom ConcreteG8Domain.D)
    (CoherentAdditionV318.reciprocal_chart_point n)
  rw [pointMap_reciprocal] at he
  exact he

lemma mapped_multiple (rho : ℚ_[p]) (hr : rho^2=2) (n j : ℤ) :
    mappedPoint p rho hr (j*n)=j • mappedPoint p rho hr n := by
  rw [mapped_actual,mapped_actual,mul_zsmul,map_zsmul]

lemma mapped_ne (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) (hn : n≠0) :
    mappedPoint p rho hr n≠0 := by
  have hu : embedding p rho hr (chartU n)≠0 := by
    intro he
    have hz := (embedding p rho hr).injective (he.trans (map_zero _).symm)
    exact hn ((CoherentMultipleCharts318.chartU_zero_iff n).mp hz)
  simp only [mappedPoint,point,dif_neg hu,ne_eq]
  intro he
  cases he

lemma actual_mem (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ)
    (hn : Near (place p rho hr) 1 (chartU n) (chartV n)) :
    mappedPoint p rho hr n∈formalSubgroup p hp (embedding p rho hr ConcreteG8Domain.D)
      (ActualSplitOrbitEntry318.coefficient_integral p rho hr) := by
  unfold mappedPoint
  apply oriented_mem
  · exact hn.1
  · have he := hn.2
    change (1:WithTop ℤ)≤Padic.addValuation (embedding p rho hr (chartV n-1)) at he
    simpa only [map_sub,map_one] using he

/-- Actual integer logarithm ratios on all signed multiples of the original
coherent point. The produced Q has the literal mappedPoint n as its carrier,
and every j•Q is the literal mappedPoint(j*n); no abstract point labels. -/
theorem integer_log_ratios (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ)
    (hn0 : n≠0) (hn : Near (place p rho hr) 1 (chartU n) (chartV n)) :
    ∃ Q : formalSubgroup p hp (embedding p rho hr ConcreteG8Domain.D)
      (ActualSplitOrbitEntry318.coefficient_integral p rho hr),
      Q.val=mappedPoint p rho hr n ∧
      ∀ j : ℤ, (j • Q).val=mappedPoint p rho hr (j*n) ∧
        logHom p hp _ _ (j • Q)/logHom p hp _ _ Q=(j:ℚ_[p]) := by
  let Q : formalSubgroup p hp (embedding p rho hr ConcreteG8Domain.D)
      (ActualSplitOrbitEntry318.coefficient_integral p rho hr) :=
    ⟨mappedPoint p rho hr n,actual_mem p hp rho hr n hn⟩
  have hQ : Q≠0 := by
    intro he
    have hv := congrArg Subtype.val he
    exact mapped_ne p rho hr n hn0 hv
  have hlog : logHom p hp _ _ Q≠0 := fun he => hQ ((ActualLogIsometry318.logHom_zero_iff p hp _ _ Q).mp he)
  refine ⟨Q,rfl,?_⟩
  intro j
  constructor
  · change j • mappedPoint p rho hr n=mappedPoint p rho hr (j*n)
    exact (mapped_multiple p rho hr n j).symm
  · rw [map_zsmul,zsmul_eq_mul]
    exact mul_div_cancel_right₀ (j:ℚ_[p]) hlog

end ActualOrientedLogMembership318
