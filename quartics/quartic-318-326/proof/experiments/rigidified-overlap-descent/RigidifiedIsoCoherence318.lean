module
public import RigidifiedRelativeClass318
public section
noncomputable section
namespace RigidifiedIsoCoherence318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (e : S ⟶ X)

/-- Identity on the actual original module sheaf, with its specified rigidification. -/
@[expose] def identity (L : RigidifiedLine e) : CompatibleIso e L L where
  iso := Iso.refl _
  commutes := by simp

/-- Composition retains the actual underlying module-sheaf composition. -/
@[expose] def compose {L M N : RigidifiedLine e}
    (f : CompatibleIso e L M) (g : CompatibleIso e M N) : CompatibleIso e L N where
  iso := f.iso ≪≫ g.iso
  commutes := by
    change (Scheme.Modules.pullback e).map (f.iso.hom ≫ g.iso.hom) ≫
      N.trivialization.hom = L.trivialization.hom
    rw [Functor.map_comp, Category.assoc, g.commutes, f.commutes]

/-- Inversion retains the actual underlying inverse module-sheaf isomorphism. -/
@[expose] def inverse {L M : RigidifiedLine e}
    (f : CompatibleIso e L M) : CompatibleIso e M L where
  iso := f.iso.symm
  commutes := by
    change ((Scheme.Modules.pullback e).mapIso f.iso).inv ≫
      L.trivialization.hom = M.trivialization.hom
    rw [← f.commutes]
    simp

lemma compose_identity {L M : RigidifiedLine e} (f : CompatibleIso e L M) :
    compose e f (identity e M) = f := by
  apply CompatibleIso.ext
  apply Iso.ext
  simp [compose, identity]

lemma identity_compose {L M : RigidifiedLine e} (f : CompatibleIso e L M) :
    compose e (identity e L) f = f := by
  apply CompatibleIso.ext
  apply Iso.ext
  simp [compose, identity]

lemma compose_assoc {L M N P : RigidifiedLine e}
    (f : CompatibleIso e L M) (g : CompatibleIso e M N) (h : CompatibleIso e N P) :
    compose e (compose e f g) h = compose e f (compose e g h) := by
  apply CompatibleIso.ext
  apply Iso.ext
  exact Category.assoc _ _ _

lemma compose_inverse {L M : RigidifiedLine e} (f : CompatibleIso e L M) :
    compose e f (inverse e f) = identity e L := by
  apply CompatibleIso.ext
  apply Iso.ext
  exact f.iso.hom_inv_id

lemma inverse_compose {L M : RigidifiedLine e} (f : CompatibleIso e L M) :
    compose e (inverse e f) f = identity e M := by
  apply CompatibleIso.ext
  apply Iso.ext
  exact f.iso.inv_hom_id

variable (p : X ⟶ S) (hs : e ≫ p = 𝟙 S) (he : Function.Bijective e.appTop)

/-- An actual compatible isomorphism chosen from the original relative-class
comparison. Its subsequent coherence is proved, not supplied as extra data. -/
@[expose] def transition {L M : RigidifiedLine e}
    (h : relativeClass p e L = relativeClass p e M) : CompatibleIso e L M :=
  Classical.choice ((relative_eq_iff_compatible p e hs he L M).mp h)

lemma transition_unique {L M : RigidifiedLine e}
    (h : relativeClass p e L = relativeClass p e M) (f : CompatibleIso e L M) :
    f = transition e p hs he h :=
  compatible_unique e he.injective L M f (transition e p hs he h)

lemma transition_refl (L : RigidifiedLine e) :
    transition e p hs he (rfl : relativeClass p e L = relativeClass p e L) =
      identity e L :=
  compatible_unique e he.injective L L _ _

/-- The cocycle equation is an equality of actual compatible isomorphisms,
not just an equality of their original line-class labels. -/
lemma transition_cocycle {L M N : RigidifiedLine e}
    (hLM : relativeClass p e L = relativeClass p e M)
    (hMN : relativeClass p e M = relativeClass p e N) :
    compose e (transition e p hs he hLM) (transition e p hs he hMN) =
      transition e p hs he (hLM.trans hMN) :=
  compatible_unique e he.injective L N _ _

lemma transition_inverse {L M : RigidifiedLine e}
    (h : relativeClass p e L = relativeClass p e M) :
    inverse e (transition e p hs he h) = transition e p hs he h.symm :=
  compatible_unique e he.injective M L _ _

/-- The equation consumed by gluing is also exposed on the original sheaf
morphisms themselves. No gluing or effectivity premise is hidden here. -/
lemma transition_hom_cocycle {L M N : RigidifiedLine e}
    (hLM : relativeClass p e L = relativeClass p e M)
    (hMN : relativeClass p e M = relativeClass p e N) :
    (transition e p hs he hLM).iso.hom ≫ (transition e p hs he hMN).iso.hom =
      (transition e p hs he (hLM.trans hMN)).iso.hom :=
  congrArg (fun f : CompatibleIso e L N => f.iso.hom)
    (transition_cocycle e p hs he hLM hMN)
end RigidifiedIsoCoherence318
