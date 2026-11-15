module
public import OriginalOpenRelativeClasses318
public import OpenLineRestriction318
public section
noncomputable section
namespace RigidifiedOpenRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (e : S ⟶ X) (e' : S' ⟶ X')
  (f : X' ⟶ X) [IsOpenImmersion f] (b : S' ⟶ S) (h : e' ≫ f = b ≫ e)

/-- Literal restriction of an original framed line, with the old frame
restriction on the whole inverse-image cover. -/
@[expose] def restrictedLine (L : Line X) : Line X' where
  object := L.object.restrict f
  Index := L.Index
  opens i := f ⁻¹ᵁ L.opens i
  cover := OpenLineRestriction318.covers f L.opens L.cover
  frame i := OpenLineRestriction318.frame f L.object (L.opens i) (L.frame i)

/-- Specified rigidification on the literal restriction object, via the
original restriction-to-pullback comparison and old pointed pullback. -/
@[expose] def line (L : RigidifiedLine e) : RigidifiedLine e' where
  line := restrictedLine f L.line
  trivialization :=
    (Scheme.Modules.pullback e').mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L.line.object) ≪≫
        (RigidifiedPointedPullback318.line e e' f b h L).trivialization

@[expose] def comparison (L : RigidifiedLine e) : CompatibleIso e'
    (line e e' f b h L) (RigidifiedPointedPullback318.line e e' f b h L) where
  iso := (Scheme.Modules.restrictFunctorIsoPullback f).app L.line.object
  commutes := rfl

/-- Literal restriction of a compatible original isomorphism remains
compatible. Its underlying map is the original restriction functor map. -/
@[expose] def mapIso {L M : RigidifiedLine e} (a : CompatibleIso e L M) :
    CompatibleIso e' (line e e' f b h L) (line e e' f b h M) where
  iso := (Scheme.Modules.restrictFunctor f).mapIso a.iso
  commutes := by
    have hh := (RigidifiedIsoCoherence318.compose e' (comparison e e' f b h L)
      (RigidifiedIsoCoherence318.compose e'
        (RigidifiedPointedPullback318.mapIso e e' f b h a)
        (RigidifiedIsoCoherence318.inverse e' (comparison e e' f b h M)))).commutes
    have hn := (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality a.iso.hom
    have he : (Scheme.Modules.restrictFunctor f).map a.iso.hom =
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app L.line.object ≫
          (Scheme.Modules.pullback f).map a.iso.hom ≫
            (Scheme.Modules.restrictFunctorIsoPullback f).inv.app M.line.object := by
      apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M.line.object)).mp
      simpa only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] using hn
    change (Scheme.Modules.pullback e').map ((Scheme.Modules.restrictFunctor f).map a.iso.hom) ≫
        (line e e' f b h M).trivialization.hom = (line e e' f b h L).trivialization.hom
    rw [he]
    exact hh
end RigidifiedOpenRestriction318
