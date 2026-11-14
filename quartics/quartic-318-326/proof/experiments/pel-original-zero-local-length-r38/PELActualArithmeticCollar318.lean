module
public import PELActualReflectedCollar318
public import PELActualAmbientProjection318
public import ChartClosedHalfNeighborhood318
public import PELOriginalSixCircleWords318
public section
noncomputable section
namespace PELActualArithmeticCollar318
open Set Filter
open scoped Topology ComplexConjugate OnePoint
open QuaternionicJointPeriodTopology318
open PELMaximalActualComplexDomain318 PELActualCanonicalBoundary318
open PELActualGeodesicPartialCharts318 PELActualSixGeodesicCharts318
open PELActualEdgeHalfNeighborhood318 PELActualReflectedCollar318
open PELActualAmbientProjection318 PELActualPuncturedQuotientMap318
open PELMaximalHalfOctagonOriginalPoints318 PELActualDomainClosure318
open PELOriginalSixCircleWords318
set_option maxHeartbeats 3200000

theorem circle_fraction (i:Fin 6) (z:ℂ) (hz:0<z.im) :
    GeodesicCircleReflection318.circleMobius (leftEndpoint i) (rightEndpoint i) z=
      (-(middle i:ℂ)*z+(constantTerm i:ℂ))/
        ((leading i:ℂ)*z-(middle i:ℂ)) := by
  have hL:(leading i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (leading_pos i).ne'
  have hden:(leading i:ℂ)*z-(middle i:ℂ)≠0 := by
    intro he
    have hh:=congrArg Complex.im he
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,sub_zero,Complex.zero_im] at hh
    exact (ne_of_gt (mul_pos (leading_pos i) hz)) hh
  have hs:(leftEndpoint i:ℂ)+(rightEndpoint i:ℂ)=2*(middle i:ℂ)/(leading i:ℂ) := by
    exact_mod_cast endpoint_sum i
  have hp:(leftEndpoint i:ℂ)*(rightEndpoint i:ℂ)=(constantTerm i:ℂ)/(leading i:ℂ) := by
    exact_mod_cast endpoint_product i
  have hd:=GeodesicCircleReflection318.denominator_ne (leftEndpoint i) (rightEndpoint i) z hz
  unfold GeodesicCircleReflection318.circleMobius
  apply (div_eq_div_iff hd hden).mpr
  push_cast
  rw [hs,show 2*(leftEndpoint i:ℂ)*(rightEndpoint i:ℂ)=
    2*((leftEndpoint i:ℂ)*(rightEndpoint i:ℂ)) by ring,hp]
  field_simp [hL]
  ring

theorem pairedPoint_original (i:Fin 6) (τ:HalfPlane) :
    pairedPoint i τ=(PELPositiveNormalizerMobius318.baseAction (sixSideWord i) τ:ℂ) := by
  rw [pairedPoint_circle i τ τ.property,original_six_action]
  exact circle_fraction i τ τ.property

theorem pairedPoint_projection (i:Fin 6) {z:ℂ} (hz:0<z.im) :
    ambientProjection (pairedPoint i z)=ambientProjection z := by
  have he:=pairedPoint_original i (⟨z,hz⟩:HalfPlane)
  rw [he,ambientProjection_upper,ambientProjection_upper (⟨z,hz⟩:HalfPlane)]
  exact maximalProjection_invariant _ _

/-- A constructed analytic germ now agrees with the ACTUAL arithmetic
map on the ENTIRE original collar: upper interior, real edge and reflected
lower side. This is stronger than boundary trace agreement. -/
theorem original_whole_collar
    (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    (hmirror:∀z∈openDomain,f (J z)=J (f z))
    {i:Fin 6} {z:ℂ} (hz:RegularEdge i z)
    (hq:ambientProjection z∈regularBase) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ ‖F z‖=1 ∧
      ∀ᶠy in 𝓝 z,ambientMap f y=ReflectedDiskJoukowski318.joukowski (F y) := by
  obtain ⟨F,hF,he,hu,hl⟩:=actual_collar_extension disk f hf hfa hmirror hz
  obtain ⟨hs,hr,hh⟩:=regular_chart hz
  have hc:=ChartClosedHalfNeighborhood318.closed_side openDomain openDomain_open (chart i) hs hh
  have hg:=CanonicalBoundaryTrace318.canonical_near_germ openDomain f F hF he
  have hpos:∀ᶠy in 𝓝 z,0<y.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.1
  have hsafe:∀ᶠy in 𝓝 z,ambientProjection y∈regularBase :=
    (ambientProjection_continuousAt hz.1).eventually (regularBase_open.mem_nhds hq)
  refine ⟨F,hF,hu,?_⟩
  filter_upwards [hl,hc,hg,hpos,hsafe] with y hyLower hyClosed hyG hyPos hySafe
  by_cases hy:0≤((chart i) y).im
  · have hyC:y∈closure openDomain:=hyClosed hy
    have hyD:y∈closedDomain:=by simpa only [closure_openDomain] using hyC
    rw [ambientMap_closed disk f hf hfa hmirror hyD hySafe]
    exact congrArg ReflectedDiskJoukowski318.joukowski (hyG hyC)
  · have hyNeg:((chart i) y).im<0:=lt_of_not_ge hy
    obtain ⟨hp,hval⟩:=hyLower hyNeg
    have hproj:=pairedPoint_projection i hyPos
    have hps:ambientProjection (pairedPoint i y)∈regularBase:=by rw [hproj];exact hySafe
    have heq:ambientMap f y=ambientMap f (pairedPoint i y) := by
      change totalMap f (ambientProjection y)=totalMap f (ambientProjection (pairedPoint i y))
      rw [hproj]
    rw [heq,ambientMap_interior disk f hf hfa hmirror hp hps]
    exact hval.symm
end PELActualArithmeticCollar318
