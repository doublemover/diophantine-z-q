module
public import PELOriginalChartUniformizer318
public import CoveringLiftLocalAction318
public import MobiusPoincarePullback318
public section
noncomputable section
namespace PELOriginalPoincareIndependence318
open Set Filter
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELEffectiveNormOneAction318 PELJointNormOneAction318
open QuaternionicUnitPeriodTransport318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open MobiusPoincarePullback318 PELOriginalChartUniformizer318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- Two analytic upper-half-plane lifts of the SAME actual original map
have the same Poincare density. The fixed original norm-one matrix is
produced from covering uniqueness, not supplied as a transition premise. -/
theorem density_eq_of_lifts (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfu : 0 < (f 0).im) (hgu : 0 < (g 0).im)
    (hq : (fun z => projection (baseChart.symm (f z))) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => projection (baseChart.symm (g z)))) :
    density f 0 = density g 0 := by
  have hft : f 0 ∈ baseChart.target := hfu
  have hgt : g 0 ∈ baseChart.target := hgu
  have hfc : ContinuousAt (fun z => baseChart.symm (f z)) 0 :=
    (baseChart.continuousAt_symm hft).comp hf.continuousAt
  have hgc : ContinuousAt (fun z => baseChart.symm (g z)) 0 :=
    (baseChart.continuousAt_symm hgt).comp hg.continuousAt
  obtain ⟨a,ha⟩ := CoveringLiftLocalAction318.exists_action projection covering
    (fun z => baseChart.symm (f z)) (fun z => baseChart.symm (g z)) 0 hfc hgc hq
  obtain ⟨u,rfl⟩ := effectiveMap_surjective a
  have hnearF := hf.continuousAt.eventually (baseChart.open_target.mem_nhds hft)
  have hnearG := hg.continuousAt.eventually (baseChart.open_target.mem_nhds hgt)
  have he : g =ᶠ[𝓝 (0 : ℂ)]
      (fun z => QuaternionicMobiusPeriods318.mobius (unitMatrix representation order u.val) (f z)) := by
    filter_upwards [ha,hnearF,hnearG] with z hz hfz hgz
    have hv := congrArg (fun t : HalfPlane => (t : ℂ)) hz
    change baseChart (baseChart.symm (g z)) =
      QuaternionicMobiusPeriods318.mobius (unitMatrix representation order u.val)
        (baseChart (baseChart.symm (f z))) at hv
    simpa only [baseChart.right_inv hfz,baseChart.right_inv hgz] using hv
  have hd : density g 0 = density
      (fun z => QuaternionicMobiusPeriods318.mobius (unitMatrix representation order u.val) (f z)) 0 := by
    unfold density
    rw [he.deriv_eq,he.self_of_nhds]
  exact (hd.trans (density_mobius _ u.property f 0 hf.differentiableAt hfu)).symm

/-- The density constructed in a given original chart is independent of
which representative of its center was chosen on the original half-plane. -/
theorem representative_independent (e : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (τ σ : HalfPlane) (hτ : projection τ = p) (hσ : projection σ = p) :
    density (uniformizer e p τ) 0 = density (uniformizer e p σ) 0 := by
  apply density_eq_of_lifts _ _
    (uniformizer_analytic e p hp he τ hτ) (uniformizer_analytic e p hp he σ hσ)
  · rw [uniformizer_zero e p hp τ hτ]; exact τ.property
  · rw [uniformizer_zero e p hp σ hσ]; exact σ.property
  · filter_upwards [projection_uniformizer e p hp τ hτ,
      projection_uniformizer e p hp σ hσ] with z htz hsz
    exact htz.2.trans hsz.2.symm

/-- Positivity and continuity are produced from actual holomorphic local
uniformizers; neither is an independent metric hypothesis. -/
theorem density_positive_continuous (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hu : 0 < (f 0).im) (hd : deriv f 0 ≠ 0) :
    0 < density f 0 ∧ ContinuousAt (density f) 0 := by
  constructor
  · exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hd)) (sq_pos_of_pos hu)
  · exact (hf.deriv.continuousAt.norm.pow 2).div
      ((Complex.continuous_im.continuousAt.comp hf.continuousAt).pow 2)
      (pow_ne_zero 2 hu.ne')
end PELOriginalPoincareIndependence318
