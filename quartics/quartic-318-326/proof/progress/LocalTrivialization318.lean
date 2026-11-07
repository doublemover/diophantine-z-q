module
public import LocalFrameEmbedding318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 Filter Topology
namespace LocalTrivialization318
set_option maxHeartbeats 0

@[expose] def framePartial (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    OpenPartialHomeomorph (Prod (sheet N hN a) ℂ) (Total (image N)) :=
  (frameMap_openEmbedding N hN a).toOpenPartialHomeomorph (frameMap N hN a)

@[expose] def baseMap (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Prod (sheet N hN a) ℂ→Prod (Base (image N)) ℂ := fun p=>(p.1.val,p.2)

theorem baseMap_openEmbedding (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    IsOpenEmbedding (baseMap N hN a) :=
  (((quotient_localHomeomorph N hN).localInverseAt a).open_source.isOpenEmbedding_subtypeVal).prodMap
    IsOpenEmbedding.id

@[expose] def basePartial (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    OpenPartialHomeomorph (Prod (sheet N hN a) ℂ) (Prod (Base (image N)) ℂ) :=
  (baseMap_openEmbedding N hN a).toOpenPartialHomeomorph (baseMap N hN a)

theorem baseMap_range (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Set.range (baseMap N hN a)=sheet N hN a ×ˢ (Set.univ:Set ℂ) := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩;exact ⟨q.1.property,Set.mem_univ _⟩
  · rintro ⟨hp,_⟩;exact ⟨(⟨p.1,hp⟩,p.2),rfl⟩

@[expose] def frameChart (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    OpenPartialHomeomorph (Total (image N)) (Prod (Base (image N)) ℂ) :=
  (framePartial N hN a).symm.trans (basePartial N hN a)

theorem frameChart_source (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    (frameChart N hN a).source=(projection (image N)) ⁻¹' sheet N hN a := by
  simp only [frameChart,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    framePartial,basePartial,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,Set.preimage_univ,Set.inter_univ]
  exact frameMap_range N hN a

theorem frameChart_target (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    (frameChart N hN a).target=sheet N hN a ×ˢ (Set.univ:Set ℂ) := by
  simp only [frameChart,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
    framePartial,basePartial,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,Set.preimage_univ,Set.inter_univ]
  exact baseMap_range N hN a

theorem frameChart_projection (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (v:Total (image N))
    (hv:v∈(frameChart N hN a).source) :
    (frameChart N hN a v).1=projection (image N) v := by
  have hv':v∈(framePartial N hN a).target := hv.1
  have he:frameMap N hN a ((framePartial N hN a).symm v)=v :=
    (framePartial N hN a).right_inv hv'
  have hp:=frameMap_projection N hN a ((framePartial N hN a).symm v)
  rw [he] at hp
  exact hp.symm

/-- Actual Mathlib local trivialization of the existing differential-orbit projection. -/
@[expose] def trivialization (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Bundle.Trivialization ℂ (projection (image N)) where
  __ := frameChart N hN a
  baseSet := sheet N hN a
  open_baseSet := ((quotient_localHomeomorph N hN).localInverseAt a).open_source
  source_eq := frameChart_source N hN a
  target_eq := frameChart_target N hN a
  proj_toFun := frameChart_projection N hN a

/-- Every actual base point has one of the constructed genuine local trivializations. -/
theorem locally_trivial (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    ∃t:Bundle.Trivialization ℂ (projection (image N)),b∈t.baseSet := by
  obtain ⟨a,rfl⟩:=quotient_surjective N b
  exact ⟨trivialization N hN a,(quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source⟩
end LocalTrivialization318
