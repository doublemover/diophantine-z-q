module
public import CotangentTransition318
public import Mathlib.Topology.FiberBundle.Basic
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 Filter Topology
namespace DependentFiberBundle318
set_option maxHeartbeats 0

abbrev fibers (N:ℕ) (b:Base (image N)) := {v:Total (image N) // projection (image N) v=b}
abbrev total (N:ℕ) := Bundle.TotalSpace ℂ (fibers N)

@[expose] def totalEquiv (N:ℕ) : total N ≃ Total (image N) where
  toFun p:=p.2.val
  invFun v:=⟨projection (image N) v,⟨v,rfl⟩⟩
  left_inv p:=by
    rcases p with ⟨b,⟨v,hv⟩⟩
    cases hv
    rfl
  right_inv v:=rfl

instance totalTopology (N:ℕ) : TopologicalSpace (total N) :=
  TopologicalSpace.induced (totalEquiv N) inferInstance

/-- The dependent total space is genuinely homeomorphic to the existing orbit quotient. -/
@[expose] def totalHomeomorph (N:ℕ) : total N ≃ₜ Total (image N) where
  __ := totalEquiv N
  continuous_toFun:=continuous_induced_dom
  continuous_invFun:=by
    apply continuous_induced_rng.mpr
    exact continuous_id

theorem total_projection (N:ℕ) (p:total N) :
    projection (image N) (totalHomeomorph N p)=p.proj := p.2.property

@[expose] def dependentTrivialization (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Bundle.Trivialization ℂ (Bundle.TotalSpace.proj (F:=ℂ) (E:=fibers N)) where
  __ := ((trivialization N hN a).compHomeomorph (totalHomeomorph N)).toOpenPartialHomeomorph
  baseSet := sheet N hN a
  open_baseSet := ((quotient_localHomeomorph N hN).localInverseAt a).open_source
  source_eq := by
    rw [((trivialization N hN a).compHomeomorph (totalHomeomorph N)).source_eq]
    ext p
    simp only [Set.mem_preimage,Function.comp_apply,total_projection]
    rfl
  target_eq := (trivialization N hN a).target_eq
  proj_toFun p hp := by
    have hh:=((trivialization N hN a).compHomeomorph (totalHomeomorph N)).proj_toFun p hp
    exact hh.trans (total_projection N p)

theorem dependentTrivialization_apply (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (p:total N) :
    dependentTrivialization N hN a p=trivialization N hN a (totalHomeomorph N p) := rfl

/-- Actual Mathlib dependent FiberBundle registration for the actual projection fibers. -/
@[expose] def fiberBundle (N:ℕ) (hN:5≤N) : FiberBundle ℂ (fibers N) where
  totalSpaceMk_isInducing' b := by
    apply (totalHomeomorph N).isInducing.of_comp_iff.mp
    exact IsInducing.subtypeVal
  trivializationAtlas' := Set.range (dependentTrivialization N hN)
  trivializationAt' b := dependentTrivialization N hN ((quotient_surjective N b).choose)
  mem_baseSet_trivializationAt' b := by
    exact Set.mem_of_eq_of_mem (quotient_surjective N b).choose_spec.symm
      (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  trivialization_mem_atlas' b := ⟨_,rfl⟩
end DependentFiberBundle318
