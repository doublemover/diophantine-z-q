module
public import PELOriginalDifferentialConstant318
public section
noncomputable section
namespace PELOriginalDifferentialPeriods318
open Set Filter
open scoped Topology
open PELOriginalInvolutionTower318 PELOriginalTorusCoverLift318
open OriginalInvolutionLegendreCharts318 PELOriginalIntegratedInvolutionCoordinates318
open PELOriginalLiftDifferential318 PELOriginalDifferentialConstant318
open PELOriginalFourBranchCoordinate318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩

/-- The actual universal lift differentiates EVERY genuine integrated
original chart to the SAME produced nonzero scalar. This pins the form,
not only the underlying topological period quotient. -/
lemma integrated_derivative (a:PELOriginalTranslationCharts318.IntegratedChart i)
    (z:ℂ) (hz:universalLift i z∈a.chart.source) :
    HasDerivAt (fun w=>a.chart (universalLift i w)) (scalar i) z := by
  have hd:=(a.derivative _ hz.2).comp z
    (coordinate_analytic i a.original z hz.1).differentiableAt.hasDerivAt
  change HasDerivAt (fun w=>a.chart (universalLift i w))
    (densityIn i a.original z) z at hd
  rw [←density_eq i a.original z hz.1,density_constant] at hd
  exact hd

/-- On every connected open piece of an actual lifted integrated chart,
the integration coordinate is EXACTLY affine, with explicit center value.
There is no unspecified sign, coordinate rescaling or overlap constant. -/
theorem integrated_affine_on_connected
    (a:PELOriginalTranslationCharts318.IntegratedChart i) (V:Set ℂ)
    (hV:IsOpen V) (hc:IsPreconnected V)
    (hsub:∀z∈V,universalLift i z∈a.chart.source) (z:ℂ) (hz:z∈V) :
    ∀w∈V,a.chart (universalLift i w)=
      a.chart (universalLift i z)+scalar i*(w-z) := by
  let f:ℂ→ℂ:=fun w=>a.chart (universalLift i w)-scalar i*w
  have hd:∀w∈V,HasDerivAt f 0 w:=by
    intro w hw
    have hh:=(integrated_derivative i a w (hsub w hw)).sub
      ((hasDerivAt_id w).const_mul (scalar i))
    simpa only [mul_one,sub_self] using hh
  intro w hw
  have he:=hV.is_const_of_deriv_eq_zero hc
    (fun q hq=>(hd q hq).differentiableAt.differentiableWithinAt)
    (fun q hq=>(hd q hq).deriv) hw hz
  change a.chart (universalLift i w)-scalar i*w=
    a.chart (universalLift i z)-scalar i*z at he
  linear_combination he

theorem integrated_affine_germ (a:PELOriginalTranslationCharts318.IntegratedChart i)
    (z:ℂ) (hz:universalLift i z∈a.chart.source) :
    ∀ᶠw in 𝓝 z,a.chart (universalLift i w)=
      a.chart (universalLift i z)+scalar i*(w-z) := by
  have ho:IsOpen ((universalLift i) ⁻¹' a.chart.source):=
    a.chart.open_source.preimage (universalLift i).continuous
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp ho z hz
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact integrated_affine_on_connected i a (Metric.ball z r) Metric.isOpen_ball
    (convex_ball z r).isPreconnected hball z (Metric.mem_ball_self hr) w hw

/-- Normalized developing coordinate of the ACTUAL original invariant
form. Its derivative has just been identified in all original charts. -/
@[expose] def developing : ℂ→+ℂ where
  toFun z:=scalar i*z
  map_zero':=mul_zero _
  map_add' z w:=mul_add _ _ _
lemma developing_injective : Function.Injective (developing i) := by
  intro z w h
  exact mul_left_cancel₀ (scalar_ne i) h
@[expose] def formPeriods : AddSubgroup ℂ:=
  (PELOriginalInvolutionActualTorus318.periods i).map (developing i)
lemma formPeriod_iff (d:ℂ) : d∈formPeriods i ↔
    ∃a∈PELOriginalInvolutionActualTorus318.periods i,scalar i*a=d :=
  AddSubgroup.mem_map

/-- Complete original lift fibers are exactly differences by the periods
of the produced differential development, not a merely included lattice. -/
theorem developed_fibers (z w:ℂ) : universalLift i z=universalLift i w ↔
    developing i z-developing i w∈formPeriods i := by
  rw [PELOriginalInvolutionActualTorus318.lift_fiber,formPeriod_iff]
  constructor
  · intro h
    refine ⟨z-w,h,?_⟩
    exact mul_sub _ _ _
  · rintro ⟨a,ha,he⟩
    have he':developing i a=developing i (z-w):=by
      change scalar i*a=scalar i*(z-w)
      rw [mul_sub]
      exact he
    exact (developing_injective i he') ▸ ha

@[expose] def periodMap : PELOriginalInvolutionActualTorus318.periods i→+formPeriods i where
  toFun a:=⟨developing i a,AddSubgroup.mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  map_zero':=Subtype.ext (map_zero (developing i))
  map_add' a b:=Subtype.ext (map_add (developing i) a.val b.val)
lemma periodMap_bijective : Function.Bijective (periodMap i):=by
  constructor
  · intro a b h
    exact Subtype.ext (developing_injective i (congrArg Subtype.val h))
  · intro d
    obtain ⟨a,ha,he⟩:=AddSubgroup.mem_map.mp d.property
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
@[expose] def periodEquiv : PELOriginalInvolutionActualTorus318.periods i≃+formPeriods i:=
  AddEquiv.ofBijective (periodMap i) (periodMap_bijective i)

/-- Full rank-two differential periods, with all integer combinations and
no omitted source periods. The basis is transported only by the explicit
nonzero coefficient of the ACTUAL original form. -/
@[expose] def integralCoordinates : RankTwoComplexHalfPeriods318.Coordinates≃+formPeriods i:=
  (CompactComplexRankTwoPeriods318.coordinates (PELOriginalInvolutionActualTorus318.periods i)).trans
    (periodEquiv i)
end PELOriginalDifferentialPeriods318
