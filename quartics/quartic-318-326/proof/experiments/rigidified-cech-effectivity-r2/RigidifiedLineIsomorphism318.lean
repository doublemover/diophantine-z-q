module
public import OriginalLineAutPullbackEquiv318
public import RelativeRigidifiedLine318
public section
noncomputable section
namespace RigidifiedLineIsomorphism318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (e : S ⟶ X)

/-- An actual isomorphism of original module sheaves that respects the two
specified actual rigidifications. -/
structure CompatibleIso (L M : RigidifiedLine e) where
  iso : L.line.object ≅ M.line.object
  commutes : ((Scheme.Modules.pullback e).mapIso iso).hom ≫ M.trivialization.hom =
    L.trivialization.hom

@[ext] lemma CompatibleIso.ext {L M : RigidifiedLine e} (f g : CompatibleIso e L M)
    (h : f.iso = g.iso) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Injective global evaluation gives uniqueness of compatible actual
isomorphisms, not just uniqueness of their class labels. -/
lemma compatible_unique (he : Function.Injective e.appTop) (L M : RigidifiedLine e)
    (f g : CompatibleIso e L M) : f = g := by
  apply CompatibleIso.ext
  apply OriginalLineAutPullbackEquiv318.pullbackIso_injective e L.line he M.line
  apply Iso.ext
  apply (cancel_mono M.trivialization.hom).mp
  exact f.commutes.trans g.commutes.symm

/-- Bijective global evaluation lifts the precise correcting automorphism,
so an actual unrigidified line isomorphism can be made compatible. -/
lemma compatible_exists (he : Function.Bijective e.appTop) (L M : RigidifiedLine e)
    (f : L.line.object ≅ M.line.object) : Nonempty (CompatibleIso e L M) := by
  let target : Aut (LineSheafPullback318.line e L.line).object := Aut.of
    (L.trivialization ≪≫ M.trivialization.symm ≪≫ ((Scheme.Modules.pullback e).mapIso f).symm)
  obtain ⟨a, ha⟩ := (OriginalLineAutPullbackEquiv318.pullbackAut_bijective e L.line he).surjective target
  have hh := congrArg (fun k : Aut (LineSheafPullback318.line e L.line).object => k.asIso.hom) ha
  change ((Scheme.Modules.pullback e).mapIso a.asIso).hom =
    L.trivialization.hom ≫ M.trivialization.inv ≫ ((Scheme.Modules.pullback e).mapIso f).inv at hh
  refine ⟨⟨a.asIso ≪≫ f, ?_⟩⟩
  change (Scheme.Modules.pullback e).map (a.asIso.hom ≫ f.hom) ≫ M.trivialization.hom = _
  rw [Functor.map_comp]
  change ((Scheme.Modules.pullback e).mapIso a.asIso).hom ≫
    ((Scheme.Modules.pullback e).mapIso f).hom ≫ M.trivialization.hom = _
  rw [hh]
  simp

lemma compatible_iff_class_eq (he : Function.Bijective e.appTop) (L M : RigidifiedLine e) :
    Nonempty (CompatibleIso e L M) ↔ classOf L.line = classOf M.line := by
  constructor
  · rintro ⟨f⟩
    exact classOf_eq f.iso
  · intro h
    obtain ⟨f⟩ := (classOf_eq_iff _ _).mp h
    exact compatible_exists e he L M f
end RigidifiedLineIsomorphism318
