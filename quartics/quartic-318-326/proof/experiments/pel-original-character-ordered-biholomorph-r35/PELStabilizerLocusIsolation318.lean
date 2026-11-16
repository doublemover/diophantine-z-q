module
public import PELStabilizerLocusInvariant318
public section
noncomputable section
namespace PELStabilizerLocusIsolation318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELOriginalStabilizerUniqueness318 PELOriginalElementaryAction318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELCoarseInertiaCoordinate318 Filter Topology
set_option maxHeartbeats 1800000

/-- No new stabilizer appears near a point with trivial actual stabilizer. -/
theorem regular_neighborhood (p : UnlevelledBase) (hp : p∉nontrivialStabilizerLocus) :
    ∃ U : Set UnlevelledBase,IsOpen U ∧ p∈U ∧ ∀ y∈U,y∉nontrivialStabilizerLocus := by
  obtain ⟨V,hV,hstab⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Labels p
  refine ⟨interior V,isOpen_interior,mem_interior_iff_mem_nhds.mpr hV,?_⟩
  intro y hy hbranch
  obtain ⟨v,hv,hfix⟩ := hbranch
  have hyp : y∈V := interior_subset hy
  have hpf := hstab (Multiplicative.ofAdd v) ⟨y,⟨⟨y,hyp,hfix⟩,hyp⟩⟩
  exact hp ⟨v,hv,hpf⟩

/-- Every actual nontrivial stabilizer point is isolated among ALL
nontrivial stabilizer points, not just those of its displayed label. -/
theorem branch_neighborhood (p : UnlevelledBase) (hp : p∈nontrivialStabilizerLocus) :
    ∃ U : Set UnlevelledBase,IsOpen U ∧ p∈U ∧
      ∀ y∈U,y∈nontrivialStabilizerLocus ↔ y=p := by
  obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective p
  obtain ⟨v,hv,hfix⟩ := hp
  obtain ⟨n,hn,ht,hpar⟩ := PELNontrivialFixedTraceZero318.fixed_trace_zero v hv τ hfix
  obtain ⟨V,hV,hstab⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Labels
    (PELUnlevelledComplexBase318.projection τ)
  have hsrc := (inertiaChart τ).open_source.mem_nhds (chart_center_source τ)
  let S : Set UnlevelledBase := {y | y∈V ∧ y∈(inertiaChart τ).source ∧
    inertiaChart τ (coarseAction n y)= -inertiaChart τ y}
  have hS : S∈𝓝 (PELUnlevelledComplexBase318.projection τ) := by
    filter_upwards [hV,hsrc,local_negation n τ hn ht] with y hy hcy hsign
    exact ⟨hy,hcy,hsign⟩
  refine ⟨interior S,isOpen_interior,mem_interior_iff_mem_nhds.mpr hS,?_⟩
  intro y hy
  constructor
  · rintro ⟨w,hw,hwfix⟩
    have hyS : y∈S := interior_subset hy
    have hwp := hstab (Multiplicative.ofAdd w) ⟨y,⟨⟨y,hyS.1,hwfix⟩,hyS.1⟩⟩
    have he : w=v := unique_nonzero_stabilizer _ w v hw hv hwp hfix
    subst w
    have hny : coarseAction n y=y := by
      rw [PELFullNormalizerAction318.actual_action_factorization,hpar]
      exact hwfix
    have hz : inertiaChart τ y=0 := by
      have h := hyS.2.2
      rw [hny] at h
      linear_combination (1/2:ℂ)*h
    apply (inertiaChart τ).injOn hyS.2.1 (chart_center_source τ)
    rw [hz,chart_center]
  · rintro rfl
    exact ⟨v,hv,hfix⟩
end PELStabilizerLocusIsolation318
