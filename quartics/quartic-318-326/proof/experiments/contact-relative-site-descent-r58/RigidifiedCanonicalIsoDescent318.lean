module
public import RigidifiedCanonicalOverlap318
public section
noncomputable section
namespace RigidifiedCanonicalIsoDescent318
open AlgebraicGeometry CategoryTheory ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedCechNerve318
open RigidifiedCanonicalOverlap318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  {L M : RigidifiedLine e}
  (a : CompatibleIso e' (pulled f g e e' square L) (pulled f g e e' square M))
  (hd : Function.Injective (doubleSection f g e e' square).appTop)

/-- Any original local pointed isomorphism automatically respects the
canonical actual double data, by rigidity on that same actual double. -/
@[expose] def hom : Hom (OriginalCanonicalDescent318.datum f L.line)
    (OriginalCanonicalDescent318.datum f M.line) where
  sheafHom := a.iso.hom
  commutes := by
    let a₀ := RigidifiedPointedPullback318.mapIso e' (doubleSection f g e e' square)
      (first f) (first g) (double_first f g e' e square) a
    let a₁ := RigidifiedPointedPullback318.mapIso e' (doubleSection f g e e' square)
      (second f) (second g) (double_second f g e' e square) a
    have hh := compatible_unique (doubleSection f g e e' square) hd _ _
      (RigidifiedIsoCoherence318.compose _ (overlap f g e e' square L) a₁)
      (RigidifiedIsoCoherence318.compose _ a₀ (overlap f g e e' square M))
    have hm := congrArg (fun b => b.iso.hom) hh
    change (overlap f g e e' square L).iso.hom ≫
        (Scheme.Modules.pullback (second f)).map a.iso.hom =
      (Scheme.Modules.pullback (first f)).map a.iso.hom ≫
        (overlap f g e e' square M).iso.hom at hm
    simpa only [overlap_hom] using hm

variable [IsAffineHom f] [Flat f] [Surjective f]

/-- The original local isomorphism descends between the unchanged original
base lines. No compatibility with unrigidified descent is assumed separately. -/
@[expose] def iso : L.line.object ≅ M.line.object :=
  OriginalGlobalLineMapDescent318.iso f a.iso (hom f g e e' square a hd) rfl

lemma iso_cover : (Scheme.Modules.pullback f).mapIso (iso f g e e' square a hd) = a.iso :=
  OriginalGlobalLineMapDescent318.iso_cover f a.iso (hom f g e e' square a hd) rfl
end RigidifiedCanonicalIsoDescent318
