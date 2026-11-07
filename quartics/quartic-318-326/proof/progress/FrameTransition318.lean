module
public import LocalTrivialization318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 Filter Topology
namespace FrameTransition318
set_option maxHeartbeats 0

theorem trivialization_frameMap (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (p:Prod (sheet N hN a) ℂ) :
    trivialization N hN a (frameMap N hN a p)=baseMap N hN a p := by
  change basePartial N hN a ((framePartial N hN a).symm (framePartial N hN a p))=_
  rw [(framePartial N hN a).left_inv (by change p∈Set.univ;trivial)]
  rfl

/-- The associated-fiber transition is exactly inverse derivative squared. -/
theorem frameMap_transition (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane)
    (b:Base (image N)) (ha:b∈sheet N hN a) (hc:b∈sheet N hN c)
    (g:image N) (hg:g • lift N hN a ⟨b,ha⟩=lift N hN c ⟨b,hc⟩) (q:ℂ) :
    frameMap N hN c (⟨b,hc⟩,q/(derivative g (lift N hN a ⟨b,ha⟩))^2)=
      frameMap N hN a (⟨b,ha⟩,q) := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  refine ⟨g,?_⟩
  apply Fiber.ext
  · exact hg
  · rfl

/-- The same rule is an equality of the actual local trivialization coordinates. -/
theorem trivialization_transition (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane)
    (b:Base (image N)) (ha:b∈sheet N hN a) (hc:b∈sheet N hN c)
    (g:image N) (hg:g • lift N hN a ⟨b,ha⟩=lift N hN c ⟨b,hc⟩) (q:ℂ) :
    trivialization N hN c (frameMap N hN a (⟨b,ha⟩,q))=
      (b,q/(derivative g (lift N hN a ⟨b,ha⟩))^2) := by
  rw [←frameMap_transition N hN a c b ha hc g hg q,trivialization_frameMap]
  rfl

theorem frameMap_norm (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (p:Prod (sheet N hN a) ℂ) :
    PeterssonQuotient318.norm (image N) (frameMap N hN a p)=
      PeterssonSectionNorm318.quadraticNorm (PoincareCurvature318.coefficient (lift N hN a p.1)) p.2 := rfl

/-- Actual local trivialization coordinates realize the descended Petersson norm. -/
theorem norm_in_trivialization (N:ℕ) (hN:5≤N) (a:UpperHalfPlane)
    (v:Total (image N)) (hv:v∈(trivialization N hN a).source) :
    PeterssonQuotient318.norm (image N) v=
      PeterssonSectionNorm318.quadraticNorm
        (PoincareCurvature318.coefficient
          ((quotient_localHomeomorph N hN).localInverseAt a (projection (image N) v)))
        (trivialization N hN a v).2 := by
  have hv':v∈(framePartial N hN a).target := hv.1
  let p:Prod (sheet N hN a) ℂ := (framePartial N hN a).symm v
  have he:frameMap N hN a p=v := (framePartial N hN a).right_inv hv'
  have hp:projection (image N) v=p.1.val := by rw [←he,frameMap_projection]
  rw [hp,←he,frameMap_norm,trivialization_frameMap]
  rfl
end FrameTransition318
