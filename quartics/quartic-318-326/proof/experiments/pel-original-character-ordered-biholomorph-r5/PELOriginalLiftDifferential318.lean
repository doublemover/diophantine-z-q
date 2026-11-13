module
public import PELOriginalInvolutionActualTorus318
public import PELOriginalTranslationCharts318
public section
noncomputable section
namespace PELOriginalLiftDifferential318
open Set Filter
open scoped Topology Manifold ContDiff
open PELOriginalInvolutionTower318 PELOriginalTorusCoverLift318
open OriginalInvolutionLegendreCharts318 PELOriginalIntegratedInvolutionCoordinates318
open PELOriginalFourBranchCoordinate318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
local instance : ChartedSpace ℂ (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involution_manifold i

@[expose] def coordinate (a:Index i):ℂ→ℂ:=fun z=>actualChart i a (universalLift i z)
@[expose] def domain (a:Index i):Set ℂ:=
  (universalLift i) ⁻¹' (actualChart i a).source
lemma domain_open (a:Index i):IsOpen (domain i a):=
  (actualChart i a).open_source.preimage (universalLift i).continuous
lemma coordinate_analytic (a:Index i) (z:ℂ) (hz:z∈domain i a):
    AnalyticAt ℂ (coordinate i a) z:=
  (contMDiffAt_iff_contDiffAt.mp ((actual_holomorphic i a _ hz).comp z
    (universalLift_holomorphic i z))).analyticAt

/-- The ORIGINAL pulled-back cotangent coefficient evaluated on the
actual universal lift, using one genuine original chart. -/
@[expose] def densityIn (a:Index i) (z:ℂ):ℂ:=
  coefficient i a (coordinate i a z)*deriv (coordinate i a) z
lemma densityIn_analytic (a:Index i) (z:ℂ) (hz:z∈domain i a):
    AnalyticAt ℂ (densityIn i a) z:=
  ((coefficient_analytic i (PELOriginalIntegratedInvolutionCoordinates318.comparison i)
    a _ ((actualChart i a).map_source hz)).comp (coordinate_analytic i a z hz)).mul
    (coordinate_analytic i a z hz).deriv

/-- Exact coordinate independence follows from the ACTUAL original
cotangent transition law and the derivative of the actual chart overlap.
No replacement differential is chosen on the produced torus. -/
lemma densityIn_eq (a b:Index i) (z:ℂ) (ha:z∈domain i a) (hb:z∈domain i b):
    densityIn i a z=densityIn i b z := by
  let A:=actualChart i a
  let B:=actualChart i b
  let T:=OriginalInvolutionLegendreCharts318.transition i
    (PELOriginalIntegratedInvolutionCoordinates318.comparison i) a b
  have ht:coordinate i a z∈T.source:=by
    refine ⟨A.map_source ha,?_⟩
    change universalLift i z∈B.source at hb
    simpa only [coordinate,A.left_inv ha] using hb
  have hv:T (coordinate i a z)=coordinate i b z:=by
    change B (A.symm (A (universalLift i z)))=B (universalLift i z)
    rw [A.left_inv ha]
  have hTa:AnalyticAt ℂ T (coordinate i a z):=by
    have hInv:=actual_inverse_holomorphic i a (coordinate i a z) (A.map_source ha)
    have hB:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω B (A.symm (coordinate i a z)):=by
      have hh:=actual_holomorphic i b (universalLift i z) hb
      simpa only [coordinate,A.left_inv ha] using hh
    exact (contMDiffAt_iff_contDiffAt.mp (hB.comp _ hInv)).analyticAt
  have he:coordinate i b=ᶠ[𝓝 z] (fun w=>T (coordinate i a w)):=by
    filter_upwards [(domain_open i a).mem_nhds ha] with w hw
    change B (universalLift i w)=B (A.symm (A (universalLift i w)))
    rw [A.left_inv hw]
  have hd:deriv (coordinate i b) z=
      deriv T (coordinate i a z)*deriv (coordinate i a) z:=
    ((hTa.differentiableAt.hasDerivAt.comp z
      (coordinate_analytic i a z ha).differentiableAt.hasDerivAt)
      .congr_of_eventuallyEq he).deriv
  have hc:=coefficient_transition i (PELOriginalIntegratedInvolutionCoordinates318.comparison i)
    a b (coordinate i a z) ht
  change coefficient i a (coordinate i a z)=coefficient i b (T (coordinate i a z))*
    deriv T (coordinate i a z) at hc
  rw [hv] at hc
  unfold densityIn
  rw [hc,hd,mul_assoc]

@[expose] def chosen (z:ℂ):Index i:=(actual_covers i (universalLift i z)).choose
lemma chosen_source (z:ℂ):z∈domain i (chosen i z):=
  (actual_covers i (universalLift i z)).choose_spec
@[expose] def density (z:ℂ):ℂ:=densityIn i (chosen i z) z
lemma density_eq (a:Index i) (z:ℂ) (hz:z∈domain i a):
    density i z=densityIn i a z:=densityIn_eq i _ a z (chosen_source i z) hz
lemma density_germ (a:Index i) (z:ℂ) (hz:z∈domain i a):
    density i=ᶠ[𝓝 z] densityIn i a:=by
  filter_upwards [(domain_open i a).mem_nhds hz] with w hw
  exact density_eq i a w hw
lemma density_analytic (z:ℂ):AnalyticAt ℂ (density i) z:=
  (densityIn_analytic i (chosen i z) z (chosen_source i z)).congr
    (density_germ i (chosen i z) z (chosen_source i z)).symm
end PELOriginalLiftDifferential318
