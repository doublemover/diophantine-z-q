module
public import AllCuspCharts318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 HolomorphicCharts318 AllCuspCharts318
open scoped Manifold ContDiff
namespace AllCuspTransitions318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual overlap with a particular filled disc is exactly that end's
original rotated cusp neighborhood. -/
theorem old_in_new (N:ℕ) (hN:5≤N) (c:End N) (b:Base (image N)) :
    original N hN b∈(newChart N hN c).source ↔
      b∈(RotatedPartialChart318.chart N hN (representative N c)).source := by
  rw [new_source,RotatedPartialChart318.chart_source]
  constructor
  · rintro ⟨q,hq⟩
    have hne:=AllCuspHausdorff318.identification_nonzero N hN b c q hq.symm
    let p:Punctures N hN:=⟨c,⟨q.val,hne,q.property⟩⟩
    have hb:b=oldMap N hN p:=
      (original_openEmbedding N hN).injective (hq.symm.trans (original_oldMap N hN p).symm)
    rw [hb,representative_region]
    exact oldMap_mem N hN p
  · intro hb
    let q:=RotatedHomeomorph318.cuspHomeomorph N hN (representative N c) ⟨b,hb⟩
    have hq:oldMap N hN ⟨c,q⟩=b:=
      congrArg Subtype.val ((RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)).symm_apply_apply ⟨b,hb⟩)
    refine ⟨inclusion N hN c q,?_⟩
    exact (original_oldMap N hN ⟨c,q⟩).symm.trans (congrArg (original N hN) hq)

theorem new_on_old (N:ℕ) (hN:5≤N) (c:End N) (b:Base (image N))
    (hb:b∈(RotatedPartialChart318.chart N hN (representative N c)).source) :
    newChart N hN c (original N hN b)=RotatedPartialChart318.chart N hN (representative N c) b := by
  let q:=RotatedHomeomorph318.cuspHomeomorph N hN (representative N c) ⟨b,hb⟩
  have hq:oldMap N hN ⟨c,q⟩=b:=
    congrArg Subtype.val ((RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)).symm_apply_apply ⟨b,hb⟩)
  have he:original N hN b=cuspChart N hN c (inclusion N hN c q):=
    (congrArg (original N hN) hq).symm.trans (original_oldMap N hN ⟨c,q⟩)
  rw [he,new_apply,RotatedPartialChart318.chart_apply]
  exact (RotatedPartialChart318.coordinateFunction_coe N hN (representative N c) ⟨b,hb⟩).symm

theorem mixed_transition (N:ℕ) (hN:5≤N) (c:End N) (b:Base (image N)) :
    letI:=complexChartedSpace N hN
    (oldChart N hN b).symm.trans (newChart N hN c) ≈
      (chartAt ℂ b).symm.trans (RotatedPartialChart318.chart N hN (representative N c)) := by
  letI:=complexChartedSpace N hN
  constructor
  · ext z
    change (z∈(chartAt ℂ b).target ∧
      original N hN ((chartAt ℂ b).symm z)∈(newChart N hN c).source) ↔
        (z∈(chartAt ℂ b).target ∧
          (chartAt ℂ b).symm z∈(RotatedPartialChart318.chart N hN (representative N c)).source)
    rw [old_in_new]
  · intro z hz
    change newChart N hN c (original N hN ((chartAt ℂ b).symm z))=
      RotatedPartialChart318.chart N hN (representative N c) ((chartAt ℂ b).symm z)
    exact new_on_old N hN c _ ((old_in_new N hN c _).mp hz.2)

theorem mixed_analytic (N:ℕ) (hN:5≤N) (c:End N) (b:Base (image N)) :
    (oldChart N hN b).symm.trans (newChart N hN c)∈contDiffGroupoid ω 𝓘(ℂ) := by
  letI:=complexChartedSpace N hN
  letI:=complex_manifold N hN
  have hc:RotatedPartialChart318.chart N hN (representative N c)∈IsManifold.maximalAtlas 𝓘(ℂ) ω (Base (image N)):=
    (RotatedPartialChart318.chart N hN (representative N c)).mem_maximalAtlas_of_contMDiffOn
      (RotatedBiholomorphic318.chart_biholomorphic N hN _).1
      (RotatedBiholomorphic318.chart_biholomorphic N hN _).2
  exact (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
    (IsManifold.compatible_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b) hc)
    (mixed_transition N hN c b)

/-- Different selected cusp charts have no transition locus. -/
theorem distinct_transition_source_empty (N:ℕ) (hN:5≤N) (c d:End N) (hcd:c≠d) :
    ((newChart N hN c).symm.trans (newChart N hN d)).source=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hc:(newChart N hN c).symm q∈(newChart N hN c).source:=
    (newChart N hN c).map_target hq.1
  have hd:(newChart N hN c).symm q∈(newChart N hN d).source:=hq.2
  rw [new_source] at hc hd
  exact Set.disjoint_left.mp (cuspCharts_disjoint N hN c d hcd) hc hd

end AllCuspTransitions318
