module
public import InverseCoordinate318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicCharts318
set_option maxHeartbeats 0

@[expose] def localChart (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    OpenPartialHomeomorph (Base (image N)) ℂ :=
  ((quotient_localHomeomorph N hN).localInverseAt a).trans ofComplex.symm

theorem localChart_apply (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (q:Base (image N)) :
    localChart N hN a q=((quotient_localHomeomorph N hN).localInverseAt a q:ℂ) := rfl

theorem localChart_symm_apply (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (w:ℂ) :
    (localChart N hN a).symm w=quotientMap N (ofComplex w) := by
  change ((quotient_localHomeomorph N hN).localInverseAt a).symm (ofComplex w)=_
  rw [(quotient_localHomeomorph N hN).localInverseAt_symm]

theorem localChart_target_positive (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (w:ℂ)
    (hw:w∈(localChart N hN a).target) : 0<w.im := by
  have hh: w∈ofComplex.symm.target := hw.1
  simp only [ofComplex,OpenPartialHomeomorph.symm_symm,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hh
  obtain ⟨z,rfl⟩:=hh
  exact z.im_pos

theorem localChart_center (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    quotientMap N a∈(localChart N hN a).source := by
  change quotientMap N a∈((quotient_localHomeomorph N hN).localInverseAt a).source ∩ _
  constructor
  · exact (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  · change (quotient_localHomeomorph N hN).localInverseAt a (quotientMap N a)∈ofComplex.symm.source
    change _∈Set.univ
    trivial

/-- Every transition of the constructed actual quotient charts is genuinely holomorphic. -/
theorem analytic_transition (N:ℕ) (hN:5≤N) (a b:UpperHalfPlane) :
    AnalyticOnNhd ℂ ((localChart N hN a).symm.trans (localChart N hN b))
      ((localChart N hN a).symm.trans (localChart N hN b)).source := by
  intro w hw
  have hpos:=localChart_target_positive N hN a w hw.1
  let z:UpperHalfPlane:=⟨w,hpos⟩
  have hb:quotientMap N z∈((quotient_localHomeomorph N hN).localInverseAt b).source := by
    have hh: (localChart N hN a).symm w∈(localChart N hN b).source := hw.2
    have hh': (localChart N hN a).symm w∈((quotient_localHomeomorph N hN).localInverseAt b).source := hh.1
    simpa only [localChart_symm_apply,ofComplex_apply_of_im_pos hpos] using hh'
  have ha:=InverseCoordinate318.analytic_localInverseAt N hN b z hb
  convert ha using 1
  ext v
  simp only [OpenPartialHomeomorph.coe_trans,Function.comp_apply,localChart_apply,localChart_symm_apply]

/-- An actual atlas containing all local quotient charts. -/
@[expose, instance_reducible] def complexChartedSpace (N:ℕ) (hN:5≤N) :
    ChartedSpace ℂ (Base (image N)) where
  atlas := Set.range (localChart N hN)
  chartAt q := localChart N hN ((quotient_surjective N q).choose)
  mem_chart_source q := by
    exact Set.mem_of_eq_of_mem (quotient_surjective N q).choose_spec.symm
      (localChart_center N hN ((quotient_surjective N q).choose))
  chart_mem_atlas q := ⟨_,rfl⟩

/-- The exact fine-level quotient is an actual complex analytic manifold.
Holomorphic transitions are derived from genuine locally constant deck transformations. -/
theorem complex_manifold (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Base (image N)) := by
  letI:=complexChartedSpace N hN
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition N hN a b).contDiffOn
      ((localChart N hN a).symm.trans (localChart N hN b)).open_source.uniqueDiffOn
end HolomorphicCharts318
