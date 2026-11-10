module
public import PELOriginalIntegratedInvolutionCoordinates318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public section
noncomputable section
namespace PELOriginalTranslationCharts318
open Set Filter
open scoped Topology
open PELOriginalInvolutionTower318 PELOriginalFourBranchCoordinate318
open PELOriginalIntegratedInvolutionCoordinates318 OriginalInvolutionLegendreCharts318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩

/-- A genuine integrated chart, retaining the original source chart and
actual derivative equal to the pulled-back invariant differential. -/
structure IntegratedChart where
  original:Index i
  primitive:OpenPartialHomeomorph ℂ ℂ
  source_subset:primitive.source⊆(actualChart i original).target
  derivative:∀z∈primitive.source,HasDerivAt primitive (coefficient i original z) z
@[expose] def IntegratedChart.chart (a:IntegratedChart i):
    OpenPartialHomeomorph (InvolutionBase i) ℂ:=
  (actualChart i a.original).trans a.primitive

/-- Every actual original point lies in a constructed integrated OPEN
partial homeomorphism, normalized to zero. The primitive's entire source
is inside the true derivative domain; germ inversion alone is not used
as a substitute for a chart. -/
theorem exists_chart (p:InvolutionBase i) :
    ∃a:IntegratedChart i,p∈a.chart.source ∧ a.chart p=0 := by
  obtain ⟨a,hp,r,hr,hsub,f,g,hf0,hfa,hfd,hga,hg0,hl,hrt⟩:=
    every_point_integrated i (comparison i) p
  let e:=actualChart i a
  let z:=e p
  have hz:z∈e.target:=e.map_source hp
  have hfa0:AnalyticAt ℂ f z:=hfa z (Metric.mem_ball_self hr)
  have hderiv:deriv f z≠0:=by
    rw [(hfd z (Metric.mem_ball_self hr)).deriv]
    exact coefficient_ne i (comparison i) a z hz
  let hd:=hfa0.hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv
  let F:OpenPartialHomeomorph ℂ ℂ:=hd.toOpenPartialHomeomorph f
  let W:Set ℂ:=e.target∩Metric.ball z r
  have hW:IsOpen W:=e.open_target.inter Metric.isOpen_ball
  let P:=F.restrOpen W hW
  have hPz:z∈P.source:=⟨hd.mem_toOpenPartialHomeomorph_source,hz,Metric.mem_ball_self hr⟩
  let A:IntegratedChart i:={
    original:=a
    primitive:=P
    source_subset:=fun _ hw=>hw.2.1
    derivative:=fun w hw=>hfd w hw.2.2 }
  refine ⟨A,⟨hp,hPz⟩,?_⟩
  exact hf0

@[expose] def transition (a b:IntegratedChart i):OpenPartialHomeomorph ℂ ℂ:=
  a.chart.symm.trans b.chart
lemma transition_value (a b:IntegratedChart i) (z:ℂ) :
    transition i a b z=b.primitive
      (OriginalInvolutionLegendreCharts318.transition i (comparison i) a.original b.original
        (a.primitive.symm z)):=rfl

/-- EVERY actual integrated overlap is locally a translation, with its
constant computed from the genuine overlap map at the same center.
The proof uses actual primitive derivative laws and the already derived
original global differential cocycle, not a postulated translation atlas. -/
theorem transition_germ (a b:IntegratedChart i) (z:ℂ)
    (hz:z∈(transition i a b).source) :
    ∀ᶠ w in 𝓝 z,transition i a b w=w+(transition i a b z-z) := by
  let T:=OriginalInvolutionLegendreCharts318.transition i (comparison i) a.original b.original
  let x:=a.primitive.symm z
  have hpa:x∈a.primitive.source:=a.primitive.map_target hz.1.1
  have hT:x∈T.source:=⟨hz.1.2,hz.2.1⟩
  have hpb:T x∈b.primitive.source:=hz.2.2
  have hf:∀ᶠ w in 𝓝 x,HasDerivAt a.primitive (coefficient i a.original w) w:=
    eventually_of_mem (a.primitive.open_source.mem_nhds hpa) (fun w hw=>a.derivative w hw)
  have hg:∀ᶠ w in 𝓝 (T x),HasDerivAt b.primitive (coefficient i b.original w) w:=
    eventually_of_mem (b.primitive.open_source.mem_nhds hpb) (fun w hw=>b.derivative w hw)
  have he:=original_translation i a.original b.original x hT a.primitive b.primitive hf hg
  have ht:ContinuousAt a.primitive.symm z:=a.primitive.continuousAt_symm hz.1.1
  filter_upwards [ht.eventually he,a.primitive.open_target.mem_nhds hz.1.1] with w hw hwp
  rw [a.primitive.right_inv hwp,a.primitive.right_inv hz.1.1] at hw
  change w-transition i a b w=z-transition i a b z at hw
  linear_combination -hw
lemma transition_derivative (a b:IntegratedChart i) (z:ℂ)
    (hz:z∈(transition i a b).source) : HasDerivAt (transition i a b) 1 z := by
  apply ((hasDerivAt_id z).add_const (transition i a b z-z)).congr_of_eventuallyEq
  exact transition_germ i a b z hz

/-- On EACH genuine connected open sub-overlap, the translation constant
is one constant throughout. Disconnected overlaps are not silently given
one sign or one period. -/
theorem translation_on_connected (a b:IntegratedChart i) (V:Set ℂ)
    (hV:IsOpen V) (hconn:IsPreconnected V) (hsub:V⊆(transition i a b).source)
    (z:ℂ) (hz:z∈V) :
    ∀w∈V,transition i a b w=w+(transition i a b z-z) := by
  let F:ℂ→ℂ:=fun w=>transition i a b w-w
  have hd:DifferentiableOn ℂ F V:=fun w hw=>
    ((transition_derivative i a b w (hsub hw)).sub (hasDerivAt_id w)).differentiableAt.differentiableWithinAt
  have hzero:V.EqOn (deriv F) 0:=by
    intro w hw
    simpa only [sub_self] using
      ((transition_derivative i a b w (hsub hw)).sub (hasDerivAt_id w)).deriv
  intro w hw
  have he:=hV.is_const_of_deriv_eq_zero hconn hd hzero hw hz
  change transition i a b w-w=transition i a b z-z at he
  linear_combination he
end PELOriginalTranslationCharts318
