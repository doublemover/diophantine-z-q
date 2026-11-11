module
public import PELOriginalPolarizationPowerBundle318
public section
noncomputable section
namespace PELOriginalPowerSectionLift318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Filter Topology
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalPolarizationAutomorphy318
open PELOriginalAutomorphyRepresentatives318
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- ALL sections of the actual original power bundle whose coefficients
are holomorphic in its genuine local trivializations. No automorphic
function or theta expansion is included in this definition. -/
structure HolomorphicSection where
  value:∀q:Base τ,PowerFiber τ hτ N q
  holomorphic:∀a:ComplexVectors,DifferentiableOn ℂ
    (fun z:ComplexVectors=>((powerCore τ hτ N).localTriv a
      ⟨projection (P τ) z,value (projection (P τ) z)⟩).2)
    (chart τ hτ a).target

@[expose] def total (s:HolomorphicSection τ hτ N)(q:Base τ):PowerTotal τ hτ N:=
  ⟨q,s.value q⟩
@[expose] def gauge (z:ComplexVectors):ℂ:=
  factor τ hτ (shiftTo τ hτ ((core τ hτ).indexAt (projection (P τ) z)) z) z^N
lemma gauge_ne_zero(z:ComplexVectors):gauge τ hτ N z≠0:=
  pow_ne_zero _ (nonzero τ hτ _ _)
/-- The scalar representative is recovered from the actual selected
bundle gauge, rather than supplied as an extra section hypothesis. -/
@[expose] def lift(s:HolomorphicSection τ hτ N)(z:ComplexVectors):ℂ:=
  (gauge τ hτ N z)⁻¹*s.value (projection (P τ) z)
lemma local_lift (s:HolomorphicSection τ hτ N)(a z:ComplexVectors)
    (ha:projection (P τ) z∈baseSet τ hτ a):
    ((powerCore τ hτ N).localTriv a (total τ hτ N s (projection (P τ) z))).2=
      factor τ hτ (shiftTo τ hτ a z) z^N*lift τ hτ N s z:=by
  let q:=projection (P τ) z
  let c:ComplexVectors:=(core τ hτ).indexAt q
  have hc:q∈baseSet τ hτ c:=(core τ hτ).mem_baseSet_at q
  have he:=factor_change τ hτ c a z hc ha
  change transition τ hτ c a q^N*s.value q=
    factor τ hτ (shiftTo τ hτ a z) z^N*
      ((factor τ hτ (shiftTo τ hτ c z) z^N)⁻¹*s.value q)
  rw [he,mul_pow]
  field_simp [pow_ne_zero N (nonzero τ hτ (shiftTo τ hτ c z) z)]

lemma target_shift_zero(a z:ComplexVectors)(hz:z∈(chart τ hτ a).target):
    shiftTo τ hτ a z=0:=by
  have ha:projection (P τ) z∈baseSet τ hτ a:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).map_target hz
  apply Subtype.ext
  rw [shiftTo_value τ hτ a z ha]
  have he:chart τ hτ a (projection (P τ) z)=z:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).right_inv hz
  simp only [he,sub_self,ZeroMemClass.coe_zero]
lemma original_chart_formula(s:HolomorphicSection τ hτ N)(a z:ComplexVectors)
    (hz:z∈(chart τ hτ a).target):
    lift τ hτ N s z=
      ((powerCore τ hτ N).localTriv a (total τ hτ N s (projection (P τ) z))).2:=by
  have ha:projection (P τ) z∈baseSet τ hτ a:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).map_target hz
  simpa only [target_shift_zero τ hτ a z hz,zero_factor,one_pow,one_mul] using
    (local_lift τ hτ N s a z ha).symm

/-- The recovered representative is genuinely entire in both complex
variables, by the supplied definition of holomorphy in ORIGINAL bundle
charts and the derived gauge-independent chart formula. -/
theorem entire(s:HolomorphicSection τ hτ N):Differentiable ℂ (lift τ hτ N s):=by
  intro z
  have hp:projection (P τ) z∈(chart τ hτ z).source:=localChart_center (P τ) z
  have hc:chart τ hτ z (projection (P τ) z)=z:=
    (quotient_localHomeomorph (P τ)).localInverseAt_apply_self
  have hz:z∈(chart τ hτ z).target:=hc ▸ (chart τ hτ z).map_source hp
  have hd:=((s.holomorphic z) z hz).differentiableAt
    ((chart τ hτ z).open_target.mem_nhds hz)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(chart τ hτ z).open_target.mem_nhds hz] with w hw
  exact original_chart_formula τ hτ N s z w hw

lemma gauge_period(z:ComplexVectors)(l:L τ hτ):
    gauge τ hτ N z=gauge τ hτ N (z+l.val)*factor τ hτ l z^N:=by
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) z)
  have ha:projection (P τ) z∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have h:=cocycle τ hτ (shiftTo τ hτ a (z+l.val)) l z
  rw [shiftTo_period τ hτ a z l ha] at h
  simpa only [gauge,projection_add_period,mul_pow,a] using congrArg (fun x:ℂ=>x^N) h
/-- Exact full original lattice rule for EVERY actual holomorphic
section, derived from its unchanged bundle gauges. -/
theorem original_automorphy(s:HolomorphicSection τ hτ N)(l:L τ hτ)(z:ComplexVectors):
    lift τ hτ N s (z+l.val)=factor τ hτ l z^N*lift τ hτ N s z:=by
  simp only [lift,projection_add_period]
  rw [gauge_period τ hτ N z l]
  field_simp [gauge_ne_zero τ hτ N (z+l.val),pow_ne_zero N (nonzero τ hτ l z)]
end PELOriginalPowerSectionLift318
