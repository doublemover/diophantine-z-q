module
public import DependentFiberBundle318
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Topology.VectorBundle.Basic
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 DependentFiberBundle318
open Filter Topology
namespace FiberLinearStructure318
set_option maxHeartbeats 0

@[expose] def frame (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN a) : fibers N b ≃ₜ ℂ :=
  (trivialization N hN a).preimageSingletonHomeomorph hb

@[expose] def chosenLift (N:ℕ) (b:Base (image N)) : UpperHalfPlane :=
  (quotient_surjective N b).choose

theorem chosenLift_mem (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    b∈sheet N hN (chosenLift N b) := by
  exact Set.mem_of_eq_of_mem (quotient_surjective N b).choose_spec.symm
    (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source

@[expose] def chosenFrame (N:ℕ) (hN:5≤N) (b:Base (image N)) : fibers N b ≃ₜ ℂ :=
  frame N hN (chosenLift N b) b (chosenLift_mem N hN b)

instance fiberAddCommGroup (N:ℕ) [hN:Fact (5≤N)] (b:Base (image N)) :
    AddCommGroup (fibers N b) := (chosenFrame N hN.out b).toEquiv.addCommGroup

instance fiberModule (N:ℕ) [hN:Fact (5≤N)] (b:Base (image N)) :
    Module ℂ (fibers N b) := (chosenFrame N hN.out b).toEquiv.addEquiv.module ℂ

@[expose] def chosenLinearEquiv (N:ℕ) [hN:Fact (5≤N)] (b:Base (image N)) :
    fibers N b ≃ₗ[ℂ] ℂ := (chosenFrame N hN.out b).toEquiv.addEquiv.linearEquiv ℂ

theorem frame_symm_val (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN a) (q:ℂ) :
    ((frame N hN a b hb).symm q).val=frameMap N hN a (⟨b,hb⟩,q) := by
  have hh:=trivialization_frameMap N hN a (⟨b,hb⟩,q)
  have hm:frameMap N hN a (⟨b,hb⟩,q)∈(trivialization N hN a).source := by
    rw [(trivialization N hN a).source_eq]
    change projection (image N) _∈sheet N hN a
    rw [frameMap_projection]
    exact hb
  change (trivialization N hN a).toOpenPartialHomeomorph.symm (b,q)=_
  change trivialization N hN a (frameMap N hN a (⟨b,hb⟩,q))=(b,q) at hh
  rw [←hh]
  exact (trivialization N hN a).left_inv hm

theorem coordinate_linear_formula (N:ℕ) [hN:Fact (5≤N)] (a:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN.out a) :
    ∃d:ℂ,∀v:fibers N b,
      (dependentTrivialization N hN.out a ⟨b,v⟩).2=chosenLinearEquiv N b v / d := by
  let c:=chosenLift N b
  let hc:=chosenLift_mem N hN.out b
  let d:ℂ:=(deriv ((HolomorphicCharts318.localChart N hN.out c).symm.trans
    (HolomorphicCharts318.localChart N hN.out a)) (lift N hN.out c ⟨b,hc⟩:ℂ))^2
  refine ⟨d,fun v=>?_⟩
  have hv:frameMap N hN.out c (⟨b,hc⟩,chosenLinearEquiv N b v)=v.val := by
    rw [←frame_symm_val]
    exact congrArg Subtype.val ((chosenFrame N hN.out b).symm_apply_apply v)
  change (trivialization N hN.out a v.val).2=_
  rw [←hv,CotangentTransition318.cotangent_square_transition N hN.out c a b hc hb]

instance dependentTrivialization_linear (N:ℕ) [hN:Fact (5≤N)] (a:UpperHalfPlane) :
    (dependentTrivialization N hN.out a).IsLinear ℂ where
  linear b hb := by
    obtain ⟨d,hd⟩:=coordinate_linear_formula N a b hb
    constructor
    · intro x y
      rw [hd,hd,hd,map_add,add_div]
    · intro c x
      rw [hd,hd,map_smul]
      change (c*_) / d=c*(_/d)
      exact mul_div_assoc c _ d

end FiberLinearStructure318
