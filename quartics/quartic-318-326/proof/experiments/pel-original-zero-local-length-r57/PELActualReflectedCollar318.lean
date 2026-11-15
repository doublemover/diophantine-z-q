module
public import LocalConformalReflectedExtension318
public import PELActualPuncturedQuotientMap318
public import GeodesicCircleReflection318
public section
noncomputable section
namespace PELActualReflectedCollar318
open Set Filter
open scoped Topology ComplexConjugate OnePoint
open PELMaximalActualComplexDomain318 PELActualCanonicalBoundary318
open PELActualGeodesicPartialCharts318 PELActualSixGeodesicCharts318
open PELActualEdgeHalfNeighborhood318
set_option maxHeartbeats 3200000

@[expose] def reflectedPoint (i:Fin 6) (z:ℂ) : ℂ :=
  (chart i).symm (conj ((chart i) z))
@[expose] def pairedPoint (i:Fin 6) (z:ℂ) : ℂ := J (reflectedPoint i z)

theorem reflectedPoint_circle (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    reflectedPoint i z=GeodesicCircleReflection318.circleReflection
      (leftEndpoint i) (rightEndpoint i) z := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  change unstraighten i (conj (straighten i z))=_
  simp only [unstraighten,straighten,map_mul,Complex.conj_ofReal,←mul_assoc,ho,one_mul]
  exact GeodesicCircleReflection318.inverse_conjugate_flatten _ _ z hz

theorem pairedPoint_circle (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    pairedPoint i z=GeodesicCircleReflection318.circleMobius
      (leftEndpoint i) (rightEndpoint i) z := by
  rw [pairedPoint,reflectedPoint_circle i z hz]
  simp [J,GeodesicCircleReflection318.circleReflection]

theorem sphere_mirror_reciprocal (w:ℂ) :
    ReflectedDiskJoukowski318.joukowski (J w)=
      ReflectedDiskJoukowski318.joukowski ((conj w)⁻¹) := by
  by_cases hw:w=0
  · simp [hw,J]
  · apply (ReflectedDiskJoukowski318.sphere_fibers _ _).mpr
    right
    have hc:conj w≠0 := by simpa using hw
    simp only [J,neg_mul,mul_inv_cancel₀ hc]

/-- Exact reciprocal lower-collar values accompany the constructed
analytic extension on every actual geodesic edge. The reflected lower
point lies in the ORIGINAL interior, not a newly declared domain. -/
theorem actual_collar_extension
    (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    (hmirror:∀z∈openDomain,f (J z)=J (f z))
    {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ F=ᶠ[𝓝[openDomain] z] f ∧ ‖F z‖=1 ∧
      ∀ᶠy in 𝓝 z,((chart i) y).im<0 →
        pairedPoint i y∈openDomain ∧
        ReflectedDiskJoukowski318.joukowski (F y)=
          ReflectedDiskJoukowski318.joukowski (f (pairedPoint i y)) := by
  obtain ⟨hs,hr,hh⟩:=regular_chart hz
  obtain ⟨F,hF,he,hu,hl⟩:=LocalConformalReflectedExtension318.local_extension_with_reflection
    openDomain openDomain_open disk f hf hfa (chart i)
    (chart_holomorphic i).1 (chart_holomorphic i).2 hs hr hh
  refine ⟨F,hF,he,hu,?_⟩
  have hconj:conj ((chart i) z)=(chart i) z := by
    apply Complex.ext <;> simp [hr]
  have hto:Tendsto (fun y=>conj ((chart i) y)) (𝓝 z) (𝓝 ((chart i) z)) := by
    simpa only [hconj] using
      (continuous_star.continuousAt.tendsto.comp ((chart i).continuousAt hs).tendsto)
  filter_upwards [hl,hto.eventually hh] with y hy hyhalf hyneg
  have hd:reflectedPoint i y∈openDomain := by
    apply hyhalf.mpr
    simpa only [Complex.conj_im] using neg_pos.mpr hyneg
  have hp:pairedPoint i y∈openDomain := (J_open _).mpr hd
  refine ⟨hp,?_⟩
  rw [hy hyneg]
  change ReflectedDiskJoukowski318.joukowski ((conj (f (reflectedPoint i y)))⁻¹)=
    ReflectedDiskJoukowski318.joukowski (f (J (reflectedPoint i y)))
  rw [hmirror _ hd]
  exact (sphere_mirror_reciprocal _).symm
end PELActualReflectedCollar318
