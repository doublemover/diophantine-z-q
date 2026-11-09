module
public import OriginalThickenedOpen318
public section
noncomputable section
namespace OriginalThickenedPointedFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 OriginalThickenedOpen318
universe u
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R) (U : X.Opens)
    [IsAffine U.toScheme] (L : Deformation R p)
@[expose] def localDeformation : Deformation R (localBase R p U) :=
  PointedLinePullback318.deformation _ _ (inclusion R p U) U.ι
    (reduction_map R (localBase R p U) p U.ι rfl) L
/-- The original line on the ENTIRE actual preimage open, with the original
special-fiber trivialization transported by its actual zero-section square. -/
@[expose] def openDeformation : PointedLineDeformation318.Deformation (localZero R p U) :=
  PointedLinePullback318.deformation _ _ (fullOpen R p U).ι U.ι (zero_square R p U) L
/-- An actual frame on the complete thickened affine open, not on a selected
smaller chart. Its comparison ends in the original pullback line. -/
@[expose] def frame : SheafOfModules.unit (fullOpen R p U).toScheme.ringCatSheaf ≅
    (openDeformation R p U L).line.object :=
  (IdentityCotangent318.pullbackUnitIso (openIso R p U).inv).symm ≪≫
    (Scheme.Modules.pullback (openIso R p U).inv).mapIso
      (OriginalAffineThickeningFrames318.frame R (localBase R p U) (localDeformation R p U L)) ≪≫
    (Scheme.Modules.pullbackComp (openIso R p U).inv (inclusion R p U)).app L.line.object ≪≫
    (Scheme.Modules.pullbackCongr (openIso_inv_inclusion R p U)).app L.line.object
/-- The actual global-unit correction on this entire open makes the local
frame compatible with the SPECIFIED original special-fiber trivialization. -/
@[expose] def pointedIso : PointedLineDeformation318.PointedIso (localZero R p U)
    (openDeformation R p U L) (PointedLineDeformation318.trivial (localZero R p U)) :=
  SplitReductionPointedKernel318.pointedIsoOfIso (localZero R p U) (localProjection R p U)
    (zero_projection R p U) (openDeformation R p U L) _ (frame R p U L).symm
/-- The original restriction frame used by the existing transition producer. -/
@[expose] def restrictionFrame : SheafOfModules.unit (fullOpen R p U).toScheme.ringCatSheaf ≅
    L.line.object.restrict (fullOpen R p U).ι :=
  (pointedIso R p U L).iso.symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (fullOpen R p U).ι).app L.line.object).symm
/-- Exact special-fiber compatibility before passing to any class quotient. -/
lemma pointed_compatibility :
    (Scheme.Modules.pullback (localZero R p U)).map (pointedIso R p U L).iso.hom ≫
      (PointedLineDeformation318.trivial (localZero R p U)).trivialization.hom =
      (openDeformation R p U L).trivialization.hom :=
  (pointedIso R p U L).compatible
end OriginalThickenedPointedFrame318
