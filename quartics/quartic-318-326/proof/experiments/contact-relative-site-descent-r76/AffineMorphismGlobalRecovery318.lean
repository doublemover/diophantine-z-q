module
public import InverseImageBasisIsoGluing318
public section
noncomputable section
namespace AffineMorphismGlobalRecovery318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

abbrev pullbackLine : X.Modules :=
  (Scheme.Modules.pullback f).obj (AffineMorphismGlobalLine318.line f D).object

@[expose] def localIso (U : Y.affineOpens) :
    (pullbackLine f D).over (sourceOpen f U) ≅ D.line.object.over (sourceOpen f U) :=
  OpenChartModuleImages318.toOverIso (sourceOpen f U) (comparison f D U)

lemma localIso_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    OpenSheafTransition318.restrictIso (localIso f D U) (f.preimage_mono h) = localIso f D V := by
  rw [localIso,← OpenSheafRestrictionCompatibility318.restriction_compatible,
    OriginalCoverRestrictionCompatibility318.comparison_nested]

/-- The constructed global base line pulls back to the unchanged original
covering line. The isomorphism is glued from the previously displayed exact
reconstruction maps on the entire inverse-image affine cover. -/
@[expose] def comparison : pullbackLine f D ≅ D.line.object :=
  InverseImageBasisIsoGluing318.iso f (pullbackLine f D) D.line.object
    (localIso f D) (localIso_nested f D)

/-- Exact recovery of every original full-chart section map, not just
existence of an isomorphism between the global objects. -/
lemma comparison_component (U : Y.affineOpens) (Z : X.Opens)
    (hZ : Z ≤ sourceOpen f U) (s : Γ(pullbackLine f D,Z)) :
    (comparison f D).hom.app Z s = OpenSheafTransition318.component (localIso f D U) Z hZ s :=
  InverseImageBasisIsoGluing318.hom_component f (pullbackLine f D) D.line.object
    (localIso f D) (localIso_nested f D) U Z hZ s

/-- Object-level global effectiveness for an affine faithfully flat
covering morphism over an arbitrary base scheme. Compatibility of this
specific global isomorphism with the original double overlap is the next
separate obligation before categorical descent is asserted. -/
theorem global_object_recovery : ∃ L : Line Y,
    Nonempty ((Scheme.Modules.pullback f).obj L.object ≅ D.line.object) :=
  ⟨AffineMorphismGlobalLine318.line f D,⟨comparison f D⟩⟩
end AffineMorphismGlobalRecovery318
