module
public import HolomorphicLineFactor318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 DependentFiberBundle318
open FiberLinearStructure318 VectorBundleRegistration318 HolomorphicCharts318 CotangentTransition318
open HolomorphicLineFactor318 Filter Topology Bundle
open scoped Manifold ContDiff
namespace LinearCocycleBinding318
set_option maxHeartbeats 0

theorem inverse_frame (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN a) (q:ℂ) :
    (dependentTrivialization N hN a).toOpenPartialHomeomorph.symm (b,q)=
      (totalHomeomorph N).symm (frameMap N hN a (⟨b,hb⟩,q)) := by
  let p:total N := (totalHomeomorph N).symm (frameMap N hN a (⟨b,hb⟩,q))
  have hp:p∈(dependentTrivialization N hN a).source := by
    apply (dependentTrivialization N hN a).mem_source.mpr
    change p.proj∈sheet N hN a
    rw [←total_projection N p]
    change projection (image N) ((totalHomeomorph N) ((totalHomeomorph N).symm _))∈_
    rw [(totalHomeomorph N).apply_symm_apply,frameMap_projection]
    exact hb
  have he:dependentTrivialization N hN a p=(b,q) := by
    rw [dependentTrivialization_apply]
    change trivialization N hN a ((totalHomeomorph N) ((totalHomeomorph N).symm _))=_
    rw [(totalHomeomorph N).apply_symm_apply,trivialization_frameMap]
    rfl
  rw [←he]
  exact (dependentTrivialization N hN a).left_inv hp

/-- The registered continuous-linear coordinate change is exactly the genuine
holomorphic inverse derivative-square scalar operator. -/
theorem coordChange_eq (N:ℕ) [hN:Fact (5≤N)] (a c:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN.out a∩sheet N hN.out c) :
    ((dependentTrivialization N hN.out a).coordChangeL ℂ
      (dependentTrivialization N hN.out c) b : ℂ→L[ℂ]ℂ)=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)
      (factor N hN.out a c b) := by
  apply ContinuousLinearMap.ext
  intro q
  change (dependentTrivialization N hN.out a).coordChangeL ℂ
    (dependentTrivialization N hN.out c) b q=_
  rw [Bundle.Trivialization.coordChangeL_apply' (R:=ℂ)
    (dependentTrivialization N hN.out a) (dependentTrivialization N hN.out c) hb q,inverse_frame N hN.out a b hb.1 q,
    dependentTrivialization_apply,(totalHomeomorph N).apply_symm_apply,
    cotangent_square_transition N hN.out a c b hb.1 hb.2 q]
  change q/(_)^2=q*((deriv ((localChart N hN.out a).symm.trans
    (localChart N hN.out c)) (localChart N hN.out a b))⁻¹)^2
  rw [div_eq_mul_inv,inv_pow]
  rfl

end LinearCocycleBinding318
