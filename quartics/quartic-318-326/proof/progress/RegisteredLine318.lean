module
public import VectorBundleRegistration318
public import Mathlib.LinearAlgebra.Dimension.Finrank
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 DependentFiberBundle318
open FiberLinearStructure318 VectorBundleRegistration318 Filter Topology Bundle
namespace RegisteredLine318
set_option maxHeartbeats 0

/-- Every actual quotient fiber has complex dimension one. -/
theorem fiber_dimension (N:ℕ) [Fact (5≤N)] (b:Base (image N)) :
    Module.finrank ℂ (fibers N b)=1 := by
  rw [(chosenLinearEquiv N b).finrank_eq,Module.finrank_self]

/-- The transferred vector-space zero is the original geometric zero orbit. -/
theorem zero_val (N:ℕ) [hN:Fact (5≤N)] (b:Base (image N)) :
    (0:fibers N b).val=PeterssonQuotient318.zeroSection (image N) b := by
  let c:=chosenLift N b
  let hc:=chosenLift_mem N hN.out b
  have hz:(frame N hN.out c b hc) (0:fibers N b)=0 :=
    (chosenLinearEquiv N b).map_zero
  have hv:frameMap N hN.out c (⟨b,hc⟩,0)=(0:fibers N b).val := by
    rw [←frame_symm_val,←hz]
    exact congrArg Subtype.val ((frame N hN.out c b hc).symm_apply_apply _)
  rw [←hv]
  have hb:quotientMap N (lift N hN.out c ⟨b,hc⟩)=b:=lift_projection N hN.out c ⟨b,hc⟩
  calc
    frameMap N hN.out c (⟨b,hc⟩,0)=PeterssonQuotient318.zeroSection (image N)
      (quotientMap N (lift N hN.out c ⟨b,hc⟩)):=rfl
    _=PeterssonQuotient318.zeroSection (image N) b:=congrArg _ hb

/-- The registered vector bundle zero section maps to the actual orbit zero section. -/
theorem total_zero_section (N:ℕ) [Fact (5≤N)] (b:Base (image N)) :
    totalHomeomorph N (Bundle.zeroSection ℂ (fibers N) b)=
      PeterssonQuotient318.zeroSection (image N) b := zero_val N b

/-- The already descended Petersson norm is nondegenerate for the registered fibers. -/
theorem fiber_norm_zero_iff (N:ℕ) [Fact (5≤N)] (b:Base (image N)) (v:fibers N b) :
    PeterssonQuotient318.norm (image N) v.val=0 ↔ v=0 := by
  rw [PeterssonQuotient318.norm_eq_zero_iff,v.property,←zero_val N b]
  exact Subtype.val_injective.eq_iff

end RegisteredLine318
