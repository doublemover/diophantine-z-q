module
public import PELOriginalLocalTargetRingMaps318
public import OpenSectionAffineTargetMap318
public section
noncomputable section
namespace PELOriginalLocalTargetSchemeMaps318
open AlgebraicGeometry CategoryTheory AffineTargetCoordinates318
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalInvariantMapOpenDescent318 PELOriginalLocalTargetRingMaps318
variable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
  (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens) (hV:IsAffineOpen V)

/-- A genuine local scheme map over the PRODUCED descended domain,
landing in the same original arbitrary target's chosen affine open. -/
@[expose] def localMap:(descendedOpen i g hg V).toScheme⟶V.toScheme:=
  OpenSectionAffineTargetMap318.toAffineOpen _ hV (targetRingMap i g hg V)
@[expose] def localMapToTarget:(descendedOpen i g hg V).toScheme⟶Z:=localMap i g hg V hV≫V.ι

/-- Exact native coordinates of the local morphism. This does not yet
identify restrictions on overlaps or assert a glued global morphism. -/
lemma localMap_coordinates:
    coordinates (localMap i g hg V hV≫hV.isoSpec.hom)=
      (descendedOpen i g hg V).topIso.inv.hom.comp (targetRingMap i g hg V):=
  OpenSectionAffineTargetMap318.coordinates_toAffineOpen _ hV _

/-- The local morphism's normalized original section map is the UNIQUE
actual pullback factor. No alternate model or assumed comparison is used. -/
lemma localMap_ring_factor:
    ((morphism i).app (descendedOpen i g hg V)).hom.comp (targetRingMap i g hg V)=
      targetSectionPullback i g hg V:=targetRingMap_square i g hg V
end PELOriginalLocalTargetSchemeMaps318
