module
public import PELOriginalInvolutionComplexAtlas318
public import LegendreIntegratedTranslations318
public import PELOriginalFourBranchCoordinate318
public import ComplexCurvePartialInverse318
public section
noncomputable section
namespace OriginalInvolutionLegendreCharts318
open Set Filter
open scoped Topology Manifold ContDiff
open PELOriginalInvolutionTower318 PELOriginalInvolutionComplexAtlas318
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open LegendreCompletedComplexAtlas318 LegendreGlobalHolomorphicDifferential318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
abbrev Target:=LegendrePlaneOverlap318.CompletedPlane (branchParameter i)
variable (H:CharacterBase i≃ₜTarget i)
abbrev Index:=InvolutionBase i×ChartIndex (branchParameter i)

/-- Actual local sheets of the ORIGINAL residual four-cover, followed by
the specified whole comparison and independently constructed target chart.
These are charts on the EXISTING source topology, not a transported space. -/
@[expose] def chart (a:Index i) : OpenPartialHomeomorph (InvolutionBase i) ℂ:=
  ((localSheet i a.1).trans H.toOpenPartialHomeomorph).trans (localChart (branchParameter i) a.2)
@[expose] def projection : InvolutionBase i→Target i:=fun x=>H (toCharacterBase i x)
lemma chart_value (a:Index i) (x:InvolutionBase i) (hx:x∈(chart i H a).source) :
    chart i H a x=localChart (branchParameter i) a.2 (projection i H x) := by
  change localChart (branchParameter i) a.2 (H (localSheet i a.1 x))=_
  rw [localSheet_value i a.1 x hx.1.1]
lemma projection_inverse (a:Index i) (z:ℂ) (hz:z∈(chart i H a).target) :
    projection i H ((chart i H a).symm z)=(localChart (branchParameter i) a.2).symm z := by
  let S:=localSheet i a.1
  let C:=localChart (branchParameter i) a.2
  have ht:H.symm (C.symm z)∈S.target:=hz.2.2
  have hv:=localSheet_value i a.1 (S.symm (H.symm (C.symm z))) (S.map_target ht)
  change H (toCharacterBase i (S.symm (H.symm (C.symm z))))=C.symm z
  rw [←hv,S.right_inv ht,H.apply_symm_apply]
lemma chart_center (p:InvolutionBase i) (j:ChartIndex (branchParameter i))
    (hj:projection i H p∈(localChart (branchParameter i) j).source) :
    p∈(chart i H (p,j)).source := by
  refine ⟨⟨localSheet_center i p,mem_univ _⟩,?_⟩
  change H (localSheet i p p)∈_
  rw [localSheet_value i p p (localSheet_center i p)]
  exact hj
lemma covers (p:InvolutionBase i) : ∃a:Index i,p∈(chart i H a).source := by
  obtain ⟨j,hj⟩:=LegendreCompletedComplexAtlas318.covers (branchParameter i) (projection i H p)
  exact ⟨(p,j),chart_center i H p j hj⟩

@[expose] def transition (a b:Index i):OpenPartialHomeomorph ℂ ℂ:=
  (chart i H a).symm.trans (chart i H b)
lemma transition_mem (a b:Index i) (z:ℂ) (hz:z∈(transition i H a b).source) :
    z∈(LegendreDifferentialChartTransitions318.Transition (branchParameter i) a.2 b.2).source := by
  refine ⟨hz.1.1,?_⟩
  have hb:=hz.2.2
  change H (localSheet i b.1 ((chart i H a).symm z))∈
    (localChart (branchParameter i) b.2).source at hb
  rw [localSheet_value i b.1 _ hz.2.1.1] at hb
  rw [show H (toCharacterBase i ((chart i H a).symm z))=
    (localChart (branchParameter i) a.2).symm z from projection_inverse i H a z hz.1] at hb
  exact hb
lemma transition_value (a b:Index i) (z:ℂ) (hz:z∈(transition i H a b).source) :
    transition i H a b z=
      LegendreDifferentialChartTransitions318.Transition (branchParameter i) a.2 b.2 z := by
  change chart i H b ((chart i H a).symm z)=_
  rw [chart_value i H b _ hz.2,projection_inverse i H a z hz.1]
  rfl
lemma transition_germ (a b:Index i) (z:ℂ) (hz:z∈(transition i H a b).source) :
    transition i H a b=ᶠ[𝓝 z]
      LegendreDifferentialChartTransitions318.Transition (branchParameter i) a.2 b.2 := by
  filter_upwards [(transition i H a b).open_source.mem_nhds hz] with w hw
  exact transition_value i H a b w hw

/-- The actual nowhere-zero target differential gives analytic coefficient
functions on EVERY whole original local sheet. Exact overlap chain rules
are inherited via equality of the actual transition maps. -/
@[expose] def coefficient (a:Index i):ℂ→ℂ:=
  (invariantDifferential (branchParameter i)).coefficient a.2
lemma coefficient_analytic (a:Index i) :
    AnalyticOnNhd ℂ (coefficient i a) (chart i H a).target :=
  fun z hz=>(invariantDifferential (branchParameter i)).analytic a.2 z hz.1
lemma coefficient_ne (a:Index i) (z:ℂ) (hz:z∈(chart i H a).target) :
    coefficient i a z≠0:=nowhere_zero (branchParameter i) a.2 z hz.1
lemma coefficient_transition (a b:Index i) (z:ℂ) (hz:z∈(transition i H a b).source) :
    coefficient i a z=coefficient i b (transition i H a b z)*deriv (transition i H a b) z := by
  have hh:=(invariantDifferential (branchParameter i)).transition a.2 b.2 z (transition_mem i H a b z hz)
  rw [←transition_value i H a b z hz,←(transition_germ i H a b z hz).deriv_eq] at hh
  exact hh

/-- Local original-coordinate primitives differ by the EXACT constant on
every genuine overlap germ. This is a construction of local translation
data, not yet a global developing map or a period lattice. -/
theorem integrated_transition (a b:Index i) (z:ℂ) (hz:z∈(transition i H a b).source)
    (f g:ℂ→ℂ)
    (hf:∀ᶠ w in 𝓝 z,HasDerivAt f (coefficient i a w) w)
    (hg:∀ᶠ w in 𝓝 (transition i H a b z),HasDerivAt g (coefficient i b w) w) :
    ∀ᶠ w in 𝓝 z,f w-g (transition i H a b w)=f z-g (transition i H a b z) := by
  have hz':=transition_mem i H a b z hz
  have hv:=transition_value i H a b z hz
  have hg':∀ᶠ w in 𝓝 (LegendreDifferentialChartTransitions318.Transition
      (branchParameter i) a.2 b.2 z),HasDerivAt g (coefficient i b w) w:=hv ▸ hg
  have he:=LegendreIntegratedTranslations318.actual_overlap_translation
    (branchParameter i) a.2 b.2 z hz' f g hf hg'
  filter_upwards [he,transition_germ i H a b z hz] with w hw htrans
  rw [htrans,hv]
  exact hw

/-- Every point of the ORIGINAL involution quotient has an actual local
primitive coordinate and inverse, normalized at that SAME point. The
primitive lives on a disk wholly inside its genuine source chart. -/
theorem every_point_integrated (p:InvolutionBase i) :
    ∃a:Index i,∃hp:p∈(chart i H a).source,
      ∃r:ℝ,0<r ∧ Metric.ball (chart i H a p) r⊆(chart i H a).target ∧
        ∃f g:ℂ→ℂ,f (chart i H a p)=0 ∧
          AnalyticOnNhd ℂ f (Metric.ball (chart i H a p) r) ∧
          (∀w∈Metric.ball (chart i H a p) r,HasDerivAt f (coefficient i a w) w) ∧
          AnalyticAt ℂ g 0 ∧ g 0=chart i H a p ∧
          (∀ᶠ w in 𝓝 (chart i H a p),g (f w)=w) ∧
          (∀ᶠ w in 𝓝 (0:ℂ),f (g w)=w) := by
  obtain ⟨a,hp⟩:=covers i H p
  let z:=chart i H a p
  have hz:z∈(chart i H a).target:=(chart i H a).map_source hp
  obtain ⟨r,hr,hrsub,f,g,hf0,hfa,hfd,hga,hg0,hl,hrt⟩:=
    LegendreIntegratedCoordinates318.exists_integrated_coordinate (branchParameter i) a.2 z hz.1
  have hopen:IsOpen ((chart i H a).target ∩ Metric.ball z r):=
    (chart i H a).open_target.inter Metric.isOpen_ball
  obtain ⟨s,hs,hsub⟩:=Metric.isOpen_iff.mp hopen z ⟨hz,Metric.mem_ball_self hr⟩
  refine ⟨a,hp,s,hs,fun w hw=>(hsub hw).1,f,g,hf0,?_,?_,hga,hg0,hl,hrt⟩
  · exact hfa.mono fun w hw=>(hsub hw).2
  · exact fun w hw=>hfd w (hsub hw).2

local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (InvolutionBase i):=involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=involution_manifold i
local instance : ChartedSpace ℂ (Target i):=LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Target i):=LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- These new integration coordinates respect the ORIGINAL source complex
atlas whenever the specified comparison is genuinely holomorphic. -/
theorem chart_holomorphic (hH:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
    (a:Index i) (x:InvolutionBase i) (hx:x∈(chart i H a).source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (chart i H a) x := by
  let C:=localChart (branchParameter i) a.2
  have hm:C∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Target i):=
    IsManifold.subset_maximalAtlas ⟨a.2,rfl⟩
  have hp:projection i H x∈C.source:=by
    have hh:=hx.2
    change H (localSheet i a.1 x)∈C.source at hh
    rw [localSheet_value i a.1 x hx.1.1] at hh
    exact hh
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y=>C (H (toCharacterBase i y))) x:=
    (contMDiffAt_of_mem_maximalAtlas hm hp).comp x
      ((hH (toCharacterBase i x)).comp x (toCharacterBase_holomorphic i x))
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chart i H a).open_source.mem_nhds hx] with y hy
  exact chart_value i H a y hy

theorem chart_inverse_holomorphic (hH:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
    (a:Index i) (z:ℂ) (hz:z∈(chart i H a).target) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (chart i H a).symm z := by
  have hp:=(chart i H a).map_target hz
  have hh:=ComplexCurvePartialInverse318.inverse_at (chart i H a)
    ((chart i H a).symm z) hp (chart_holomorphic i H hH a _ hp)
  simpa only [(chart i H a).right_inv hz] using hh
end OriginalInvolutionLegendreCharts318
