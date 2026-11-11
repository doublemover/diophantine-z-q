module
public import RigidifiedEffectiveDescent318
public section
noncomputable section
namespace RigidifiedFaithfulDetection318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  [IsAffineHom g] [Flat g] [Surjective g]
  {L M : RigidifiedLine e}

/-- Compatibility with a specified rigidification is detected by the
original faithfully flat base cover. The original ambient isomorphism is
retained unchanged; the map on total spaces need not itself be a cover. -/
@[expose] def descendCompatibility (a : L.line.object ≅ M.line.object)
    (h : CompatibleIso e'
      (RigidifiedPointedPullback318.line e e' f g square L)
      (RigidifiedPointedPullback318.line e e' f g square M))
    (ha : h.iso = (Scheme.Modules.pullback f).mapIso a) : CompatibleIso e L M where
  iso := a
  commutes := by
    apply GlobalAffineLineFaithfulness318.pullback_injective g
    rw [Functor.map_comp]
    have hn := (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.naturality a.hom
    change (Scheme.Modules.pullback e').map ((Scheme.Modules.pullback f).map a.hom) ≫
        (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app M.line.object =
      (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app L.line.object ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback e).map a.hom) at hn
    have hh := h.commutes
    rw [ha] at hh
    change (Scheme.Modules.pullback e').map ((Scheme.Modules.pullback f).map a.hom) ≫
        (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app M.line.object ≫
        (Scheme.Modules.pullback g).map M.trivialization.hom ≫
        (IdentityCotangent318.pullbackUnitIso g).hom =
      (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app L.line.object ≫
        (Scheme.Modules.pullback g).map L.trivialization.hom ≫
        (IdentityCotangent318.pullbackUnitIso g).hom at hh
    rw [← Category.assoc,← Category.assoc,hn] at hh
    simp only [Category.assoc] at hh
    apply (cancel_epi
      ((RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app L.line.object)).mp
    apply (cancel_mono ((IdentityCotangent318.pullbackUnitIso g).hom)).mp
    simpa only [Category.assoc,Functor.mapIso_hom] using hh
end RigidifiedFaithfulDetection318
