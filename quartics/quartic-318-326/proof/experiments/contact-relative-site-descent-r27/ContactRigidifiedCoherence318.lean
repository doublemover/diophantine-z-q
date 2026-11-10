module
public import RigidifiedClassQuotient318
public import ContactFieldRigidifiedClass318
public section
noncomputable section
namespace ContactRigidifiedCoherence318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318 RigidifiedRelativeClass318 RigidifiedIsoCoherence318
open ContactFieldRigidifiedClass318
variable (c : Fin 4 → ℚˣ) (t : ℚ)

/-- The exact original contact-field relative quotient is the quotient by
actual rigidification-compatible isomorphisms, with all hypotheses discharged. -/
@[expose] def classEquivalence :
    RigidifiedClassQuotient318.RigidifiedClass (e c t) ≃
      RelativeLineClassQuotient318.RelativeClass (p c t) :=
  RigidifiedClassQuotient318.equivalence (e c t) (p c t)
    (section_eq c t) (section_appTop_bijective c t)

/-- Coherent actual comparison maps for every indexed collection of rigidified
lines on the whole original contact field family representing a common class.
The index type is unrestricted; no cover or overlap is silently assumed. -/
@[expose] def transitionFamily {I : Type*} (L : I → RigidifiedLine (e c t))
    (q : RelativeLineClassQuotient318.RelativeClass (p c t))
    (h : ∀ i, relativeClass (p c t) (e c t) (L i) = q) (i j : I) :
    CompatibleIso (e c t) (L i) (L j) :=
  transition (e c t) (p c t) (section_eq c t) (section_appTop_bijective c t)
    ((h i).trans (h j).symm)

lemma transitionFamily_refl {I : Type*} (L : I → RigidifiedLine (e c t))
    (q : RelativeLineClassQuotient318.RelativeClass (p c t))
    (h : ∀ i, relativeClass (p c t) (e c t) (L i) = q) (i : I) :
    transitionFamily c t L q h i i = identity (e c t) (L i) :=
  compatible_unique (e c t) (section_appTop_bijective c t).injective (L i) (L i) _ _

/-- This is the actual module-sheaf cocycle equation on the original source,
not merely the cocycle equation in its relative class group. -/
theorem transitionFamily_cocycle {I : Type*} (L : I → RigidifiedLine (e c t))
    (q : RelativeLineClassQuotient318.RelativeClass (p c t))
    (h : ∀ i, relativeClass (p c t) (e c t) (L i) = q) (i j k : I) :
    (transitionFamily c t L q h i j).iso.hom ≫
      (transitionFamily c t L q h j k).iso.hom =
        (transitionFamily c t L q h i k).iso.hom := by
  have hc : compose (e c t) (transitionFamily c t L q h i j)
      (transitionFamily c t L q h j k) = transitionFamily c t L q h i k :=
    compatible_unique (e c t) (section_appTop_bijective c t).injective (L i) (L k) _ _
  exact congrArg (fun f : CompatibleIso (e c t) (L i) (L k) => f.iso.hom) hc

/-- Changing how comparison isomorphisms are obtained cannot change the actual
maps, provided they respect the same specified rigidifications. -/
theorem transitionFamily_unique {I : Type*} (L : I → RigidifiedLine (e c t))
    (q : RelativeLineClassQuotient318.RelativeClass (p c t))
    (h : ∀ i, relativeClass (p c t) (e c t) (L i) = q)
    (f : ∀ i j, CompatibleIso (e c t) (L i) (L j)) (i j : I) :
    f i j = transitionFamily c t L q h i j :=
  compatible_unique (e c t) (section_appTop_bijective c t).injective (L i) (L j) _ _
end ContactRigidifiedCoherence318
