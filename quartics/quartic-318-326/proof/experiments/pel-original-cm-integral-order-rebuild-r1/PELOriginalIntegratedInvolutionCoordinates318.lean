module
public import OriginalInvolutionLegendreCharts318
public import PELOriginalCompletedBiholomorph318
public section
noncomputable section
namespace PELOriginalIntegratedInvolutionCoordinates318
open Set Filter
open scoped Topology Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalInvolutionTower318 PELOriginalInvolutionComplexAtlas318
open OriginalInvolutionLegendreCharts318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
local instance : ChartedSpace ℂ (InvolutionBase i):=involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=involution_manifold i

/-- No supplied curve uniformization: this is the constructed comparison
of the SAME original character quotient with the independent Legendre
model. The residual four-cover remains the literal original quotient map. -/
@[expose] def comparison:=PELOriginalCompletedBiholomorph318.comparison i
@[expose] def actualChart (a:Index i):OpenPartialHomeomorph (InvolutionBase i) ℂ:=
  chart i (comparison i) a
lemma actual_covers (p:InvolutionBase i):∃a:Index i,p∈(actualChart i a).source:=
  covers i (comparison i) p
lemma actual_holomorphic (a:Index i) (p:InvolutionBase i) (hp:p∈(actualChart i a).source):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (actualChart i a) p:=
  chart_holomorphic i (comparison i) (PELOriginalCompletedBiholomorph318.forward_holomorphic i) a p hp
lemma actual_inverse_holomorphic (a:Index i) (z:ℂ) (hz:z∈(actualChart i a).target):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (actualChart i a).symm z:=
  chart_inverse_holomorphic i (comparison i) (PELOriginalCompletedBiholomorph318.forward_holomorphic i) a z hz

/-- The pullback of the actual Legendre invariant form is a genuine
nowhere-zero holomorphic cotangent section on the WHOLE original
involution quotient: coefficients, all overlap chain laws and nonzero
values are constructed, including points above finite branches/infinity. -/
theorem original_differential :
    (∀a:Index i,AnalyticOnNhd ℂ (coefficient i a) (actualChart i a).target) ∧
    (∀a:Index i,∀z∈(actualChart i a).target,coefficient i a z≠0) ∧
    (∀a b:Index i,∀z∈(transition i (comparison i) a b).source,
      coefficient i a z=coefficient i b (transition i (comparison i) a b z)*
        deriv (transition i (comparison i) a b) z) :=
  ⟨coefficient_analytic i (comparison i),coefficient_ne i (comparison i),
    coefficient_transition i (comparison i)⟩

/-- Actual integrated ORIGINAL source coordinates and a genuine analytic
inverse at every point. The source topology and original complex atlas
are unchanged, and every derivative is the actual pulled-back invariant
form. This prepares global development but does not postulate its periods. -/
theorem original_local_integral (p:InvolutionBase i) :
    ∃q:InvolutionBase i→ℂ,∃g:ℂ→InvolutionBase i,
      q p=0 ∧ g 0=p ∧
      ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω q p ∧
      ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g 0 ∧
      (∀ᶠ x in 𝓝 p,g (q x)=x) ∧
      (∀ᶠ w in 𝓝 (0:ℂ),q (g w)=w) := by
  obtain ⟨a,hp,r,hr,hsub,f,k,hf0,hfa,hfd,hka,hk0,hl,hrt⟩:=
    every_point_integrated i (comparison i) p
  let e:=actualChart i a
  let z:=e p
  have hz:z∈e.target:=e.map_source hp
  have hf:AnalyticAt ℂ f z:=hfa z (Metric.mem_ball_self hr)
  let q:InvolutionBase i→ℂ:=fun x=>f (e x)
  let g:ℂ→InvolutionBase i:=fun w=>e.symm (k w)
  have hq0:q p=0:=hf0
  have hg0:g 0=p:=by
    change e.symm (k 0)=p
    rw [hk0]
    exact e.left_inv hp
  have hq:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω q p:=
    (contMDiffAt_iff_contDiffAt.mpr hf.contDiffAt).comp p (actual_holomorphic i a p hp)
  have hinv:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm (k 0):=by
    rw [hk0]
    exact actual_inverse_holomorphic i a z hz
  have hg:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g 0:=
    hinv.comp 0 (contMDiffAt_iff_contDiffAt.mpr hka.contDiffAt)
  refine ⟨q,g,hq0,hg0,hq,hg,?_,?_⟩
  · filter_upwards [(e.continuousAt hp).eventually hl,e.open_source.mem_nhds hp] with x hx hxe
    change e.symm (k (f (e x)))=x
    rw [hx]
    exact e.left_inv hxe
  · have hkt:∀ᶠ w in 𝓝 (0:ℂ),k w∈e.target:=
      hka.continuousAt.eventually (by simpa only [hk0] using e.open_target.mem_nhds hz)
    filter_upwards [hrt,hkt] with w hw htw
    change f (e (e.symm (k w)))=w
    rw [e.right_inv htw]
    exact hw

/-- Original integrated overlap changes are translations with the exact
center constant, derived from the actual global differential cocycle. -/
theorem original_translation (a b:Index i) (z:ℂ)
    (hz:z∈(transition i (comparison i) a b).source) (f g:ℂ→ℂ)
    (hf:∀ᶠ w in 𝓝 z,HasDerivAt f (coefficient i a w) w)
    (hg:∀ᶠ w in 𝓝 (transition i (comparison i) a b z),HasDerivAt g (coefficient i b w) w) :
    ∀ᶠ w in 𝓝 z,f w-g (transition i (comparison i) a b w)=
      f z-g (transition i (comparison i) a b z) :=
  integrated_transition i (comparison i) a b z hz f g hf hg
end PELOriginalIntegratedInvolutionCoordinates318
