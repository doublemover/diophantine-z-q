module
public import FiberQuotientCovering318
public import Mathlib.Topology.FiberBundle.Trivialization
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open Filter Topology
namespace LocalFrameEmbedding318
set_option maxHeartbeats 0

@[expose] def sheet (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) : Set (Base (image N)) :=
  ((quotient_localHomeomorph N hN).localInverseAt a).source

instance sheetNonempty (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) : Nonempty (sheet N hN a) :=
  ⟨⟨quotientMap N a,(quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source⟩⟩

@[expose] def lift (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (b:sheet N hN a) : UpperHalfPlane :=
  (quotient_localHomeomorph N hN).localInverseAt a b

theorem lift_projection (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (b:sheet N hN a) :
    quotientMap N (lift N hN a b)=b.val :=
  (quotient_localHomeomorph N hN).apply_localInverseAt_of_mem b.property

@[expose] def frameMap (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Prod (sheet N hN a) ℂ → Total (image N) :=
  fun p=>totalQuotientMap N ⟨lift N hN a p.1,p.2⟩

theorem frameMap_projection (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) (p:Prod (sheet N hN a) ℂ) :
    projection (image N) (frameMap N hN a p)=p.1.val :=
  lift_projection N hN a p.1

theorem frameMap_injective (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Function.Injective (frameMap N hN a) := by
  rintro ⟨b,q⟩ ⟨c,r⟩ he
  have hb:b=c := by
    apply Subtype.ext
    simpa only [frameMap_projection] using congrArg (projection (image N)) he
  subst c
  have hv:q=r := by
    apply fiberParam_injective (image N) (lift N hN a b)
      (image_fixed_eq_one N hN · · (lift N hN a b))
    apply Subtype.ext
    exact he
  subst r
  rfl

/-- The actual local coefficient map is an open embedding into the actual orbit total space. -/
theorem frameMap_openEmbedding (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    IsOpenEmbedding (frameMap N hN a) := by
  have he:IsOpenEmbedding (lift N hN a) :=
    ((quotient_localHomeomorph N hN).localInverseAt a).isOpenEmbedding_restrict
  have hp:IsOpenEmbedding (fun p:Prod (sheet N hN a) ℂ=>Fiber.mk (lift N hN a p.1) p.2) :=
    coordinateHomeomorph.symm.isOpenEmbedding.comp (he.prodMap IsOpenEmbedding.id)
  exact ((total_localHomeomorph N hN).comp hp.isLocalHomeomorph).isOpenEmbedding_of_injective
    (frameMap_injective N hN a)

/-- Its image is exactly the actual total space lying above the chosen quotient sheet. -/
theorem frameMap_range (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    Set.range (frameMap N hN a)=(projection (image N)) ⁻¹' sheet N hN a := by
  ext v
  constructor
  · rintro ⟨p,rfl⟩
    change projection (image N) (frameMap N hN a p)∈sheet N hN a
    rw [frameMap_projection]
    exact p.1.property
  · intro hv
    let b:sheet N hN a:=⟨projection (image N) v,hv⟩
    have hp:projection (image N) v=(⟦lift N hN a b⟧:Base (image N)) :=
      (lift_projection N hN a b).symm
    obtain ⟨q,hq⟩:=fiberParam_surjective (image N) (lift N hN a b) ⟨v,hp⟩
    exact ⟨(b,q),congrArg Subtype.val hq⟩
end LocalFrameEmbedding318
