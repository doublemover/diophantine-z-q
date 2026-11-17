module
public import AffineOpenPointTransport318
public import PELOriginalSpectrumPrimeOrbits318
public section
noncomputable section
namespace PELOriginalAffineFiberOrbits318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=
  PELOriginalWholeCharacterFinite318.finite i

/-- On every actual target affine open, the FULL inverse image is affine
by finiteness. Every actual scheme-point fiber there is an original-kernel
orbit, via the native fromSpec comparison and actual appLE square. -/
theorem affine_fiber_orbit (i:Fin 4) (U:(Curve i).Opens) (hU:IsAffineOpen U)
    (p q:Model) (hp:morphism i p∈U) (hq:morphism i q∈U)
    (he:morphism i p=morphism i q):
    ∃a:Kernel i,schemeDeck a.val p=q:=by
  let hV:IsAffineOpen (morphism i⁻¹ᵁU):=hU.preimage (morphism i)
  obtain ⟨P,hP⟩:=AffineOpenPointTransport318.exists_prime hV p hp
  obtain ⟨Q,hQ⟩:=AffineOpenPointTransport318.exists_prime hV q hq
  have hPQ:Spec.map ((morphism i).app U) P=Spec.map ((morphism i).app U) Q:=by
    apply AffineOpenPointTransport318.fromSpec_injective hU
    rw [AffineOpenPointTransport318.app_point (morphism i) hU hV,
      AffineOpenPointTransport318.app_point (morphism i) hU hV,hP,hQ,he]
  obtain ⟨a,ha⟩:=PELOriginalSpectrumPrimeOrbits318.spectrum_fiber_orbit i U P Q hPQ
  refine ⟨a,?_⟩
  have hs:=AffineOpenPointTransport318.appLE_point (schemeDeck a.val) hV hV
    (preimage_stable i U a.val a.property).ge P
  change hV.fromSpec
    (Spec.map (CommRingCat.ofHom (sectionAction i U a.val a.property)) P)=
      schemeDeck a.val (hV.fromSpec P) at hs
  rw [ha,hQ,hP] at hs
  exact hs.symm
end PELOriginalAffineFiberOrbits318
