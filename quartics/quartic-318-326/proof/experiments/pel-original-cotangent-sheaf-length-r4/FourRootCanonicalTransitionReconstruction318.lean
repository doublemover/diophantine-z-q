module
public import FourRootActualCanonicalLine318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace FourRootCanonicalTransitionReconstruction318
open AlgebraicGeometry CategoryTheory Opposite
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318 FourRootActualCanonicalLine318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
/-- Actual units on COMPLETE overlaps of the original five canonical
opens, extracted from the produced intrinsic sheaf frames. -/
@[expose] def transitions:=LineFrameCocycle318.cocycle (omega b) (opens b hb) (frame b hb)
lemma actual_overlap (i j:Option (Fin 4)) (W:(scheme b).Opens)
    (h:W≤opens b hb i⊓opens b hb j)(s:Γ(scheme b,W)):
    OpenLineFrameCoordinates318.frame (omega b) (opens b hb i) (frame b hb i) W
      (h.trans inf_le_left)
      (((scheme b).presheaf.map (homOfLE h).op ((transitions b hb).transition i j).val)*s)=
    OpenLineFrameCoordinates318.frame (omega b) (opens b hb j) (frame b hb j) W
      (h.trans inf_le_right) s:=
  LineFrameCocycle318.relation (omega b) (opens b hb) (frame b hb) i j W h s
/-- Effective reconstruction preserves the SAME original intrinsic Omega,
not merely pointwise ranks or an asserted abstract line-bundle class. -/
@[expose] def reconstruction:
    omega b≅CocycleModule318.object (opens b hb) (transitions b hb):=
  LineFrameReconstructionIso318.iso (omega b) (opens b hb) (frame b hb) (cover_top b hb)
lemma original_frame(i:Option (Fin 4)):
    (Scheme.Modules.restrictFunctor (opens b hb i).ι).map (reconstruction b hb).hom≫
      CocycleActualLocalFrame318.transpose (opens b hb) (transitions b hb) i=
      (frame b hb i).inv:=
  LineFrameReconstructionIso318.original_frame (omega b) (opens b hb) (frame b hb)
    (cover_top b hb) i
end FourRootCanonicalTransitionReconstruction318
