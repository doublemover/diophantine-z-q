module
public import ProperGlobalSections318
public import IntrinsicGlobalInvariantGenerator318
public section
noncomputable section
namespace IntrinsicConstantInvariantGenerator318
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Constants enter through the original structural map and the actual
Spec/global-sections equivalence, with no inferred scalar action. -/
@[expose] def constant (A B : R) : R →+* Γ(WeierstrassGluing318.scheme A B, ⊤) :=
  (WeierstrassGluing318.structureMap A B).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
lemma constant_bijective (A B : R) : Function.Bijective (constant A B) :=
  (ProperGlobalSections318.family_appTop_bijective A B).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
/-- The specified invariant generates the entire original global Omega space
uniquely over base constants, for the completed family over a domain. -/
theorem bijective (A B : R) (hD : IsUnit (-16 * (4 * A^3 + 27 * B^2))) :
    Function.Bijective (fun a : R => constant A B a • IntrinsicGlobalFrame318.invariant A B hD) :=
  (IntrinsicGlobalInvariantGenerator318.bijective A B hD).comp (constant_bijective A B)
theorem existsUnique (A B : R) (hD : IsUnit (-16 * (4 * A^3 + 27 * B^2)))
    (s : Γ(FamilyIntrinsicDifferentials318.familyOmega A B, ⊤)) :
    ∃! a : R, constant A B a • IntrinsicGlobalFrame318.invariant A B hD = s := by
  obtain ⟨a, ha⟩ := (bijective A B hD).surjective s
  exact ⟨a, ha, fun b hb => (bijective A B hD).injective (hb.trans ha.symm)⟩
end IntrinsicConstantInvariantGenerator318
