module
public import PELOriginalPolarizationLineBundle318
public import PELOriginalMetricSmoothCoefficient318
public section
noncomputable section
namespace PELOriginalDescendedMetric318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPolarizationMetric318
open Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- Exact metric compatibility on every TRUE overlap of the original
quotient covering charts. The same automorphy factor as the bundle is used. -/
lemma overlap_metric (a b:ComplexVectors) (q:Base τ)
    (ha:q∈baseSet τ hτ a) (hb:q∈baseSet τ hτ b) (v:ℂ):
    squaredNorm τ hτ (chart τ hτ b q,transition τ hτ a b q*v)=
      squaredNorm τ hτ (chart τ hτ a q,v):=by
  have hs:chart τ hτ a q+(shift τ hτ a b q:ComplexVectors)=chart τ hτ b q:=by
    rw [shift_value τ hτ a b q ha hb]
    abel
  have h:=squaredNorm_action τ hτ (shift τ hτ a b q) (chart τ hτ a q,v)
  simpa only [action,transition,hs] using h

/-- Positive squared Hermitian norm on the ACTUAL produced bundle.
The core's selected fiber representative is used only for the definition;
every genuine local trivialization computes the same value below. -/
@[expose] def metric (p:Total τ hτ):ℝ:=
  squaredNorm τ hτ (chart τ hτ ((core τ hτ).indexAt p.1) p.1,p.2)
lemma local_formula (a:ComplexVectors) (p:Total τ hτ)
    (hp:p.1∈baseSet τ hτ a):
    metric τ hτ p=squaredNorm τ hτ
      (chart τ hτ a p.1,((core τ hτ).localTriv a p).2):=by
  symm
  exact overlap_metric τ hτ ((core τ hτ).indexAt p.1) a p.1
    ((core τ hτ).mem_baseSet_at p.1) hp p.2
lemma nonnegative (p:Total τ hτ):0≤metric τ hτ p:=
  squaredNorm_nonnegative τ hτ _
lemma zero_iff (p:Total τ hτ):metric τ hτ p=0↔p.2=0:=
  squaredNorm_zero_iff τ hτ _
lemma positive (p:Total τ hτ) (hp:p.2≠0):0<metric τ hτ p:=
  lt_of_le_of_ne (nonnegative τ hτ p) (Ne.symm ((zero_iff τ hτ p).not.mpr hp))
lemma fiber_scaling (q:Base τ) (a:ℂ) (v:Fiber τ hτ q):
    metric τ hτ ⟨q,a • v⟩=‖a‖^2*metric τ hτ ⟨q,v⟩:=by
  change ‖a*v‖^2*_=‖a‖^2*(‖v‖^2*_)
  rw [norm_mul,mul_pow,mul_assoc]

/-- Actual bundle-trivialization inverse, not a newly chosen fiber
identification. Thus these coefficients define a metric on the same line. -/
lemma inverse_local_formula (a:ComplexVectors) (q:Base τ)
    (hq:q∈baseSet τ hτ a) (v:ℂ):
    metric τ hτ ⟨q,(core τ hτ).coordChange a ((core τ hτ).indexAt q) q v⟩=
      squaredNorm τ hτ (chart τ hτ a q,v):=by
  exact overlap_metric τ hτ a ((core τ hτ).indexAt q) q hq
    ((core τ hτ).mem_baseSet_at q) v
lemma continuous_metric:Continuous (metric τ hτ):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  have hp:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at p.1
  have hproj:ContinuousAt (fun x:Total τ hτ=>x.1) p:=
    (projection_continuous τ hτ).continuousAt
  have htriv:ContinuousAt ((core τ hτ).localTriv a) p:=
    (core τ hτ).localTriv a |>.continuousAt hp
  have h:ContinuousAt (fun x:Total τ hτ=>squaredNorm τ hτ
      (chart τ hτ a x.1,((core τ hτ).localTriv a x).2)) p:=
    (PELOriginalMetricSmoothCoefficient318.smooth_local_metric τ hτ).continuous.continuousAt.comp p
      (((chart τ hτ a).continuousAt hp).comp p hproj |>.prodMk htriv.snd)
  apply h.congr_of_eventuallyEq
  filter_upwards [hproj ((chart τ hτ a).open_source.mem_nhds hp)] with x hx
  exact (local_formula τ hτ a x hx).symm

/-- Smoothness in EVERY original complex base chart and actual bundle
fiber coordinate. Equality is on the full chart domain, not at its center. -/
lemma original_smooth_formula (a:ComplexVectors) (z:ComplexVectors)
    (hz:z∈(chart τ hτ a).target) (v:ℂ):
    metric τ hτ ⟨projection (P τ) z,
      (core τ hτ).coordChange a
        ((core τ hτ).indexAt (projection (P τ) z)) (projection (P τ) z) v⟩=
      squaredNorm τ hτ (z,v):=by
  have hq:projection (P τ) z∈baseSet τ hτ a:=by
    have h:=(chart τ hτ a).map_target hz
    simpa only [chart,localChart_symm] using h
  rw [inverse_local_formula τ hτ a _ hq]
  have h:=(chart τ hτ a).right_inv hz
  simpa only [chart,localChart_symm] using congrArg (fun w=>squaredNorm τ hτ (w,v)) h
theorem smooth_in_original_coordinates (a:ComplexVectors):
    ContDiffOn ℝ ⊤ (fun p:ComplexVectors×ℂ=>
      metric τ hτ ⟨projection (P τ) p.1,
        (core τ hτ).coordChange a
          ((core τ hτ).indexAt (projection (P τ) p.1)) (projection (P τ) p.1) p.2⟩)
      ((chart τ hτ a).target×ˢSet.univ):=by
  apply (PELOriginalMetricSmoothCoefficient318.smooth_local_metric τ hτ).contDiffOn.congr
  intro p hp
  exact original_smooth_formula τ hτ a p.1 hp.1 p.2
end PELOriginalDescendedMetric318
