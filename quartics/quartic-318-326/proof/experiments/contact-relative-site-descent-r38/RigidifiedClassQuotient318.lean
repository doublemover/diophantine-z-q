module
public import RigidifiedIsoCoherence318
public section
noncomputable section
namespace RigidifiedClassQuotient318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318 RigidifiedRelativeClass318 RigidifiedIsoCoherence318
open RelativeLineClassQuotient318
universe u
variable {X S : Scheme.{u}} (e : S ⟶ X)

/-- Actual rigidification-compatible isomorphism, before any sheafification. -/
@[expose] def compatibleSetoid : Setoid (RigidifiedLine e) where
  r L M := Nonempty (CompatibleIso e L M)
  iseqv := ⟨fun L => ⟨identity e L⟩,
    fun ⟨f⟩ => ⟨inverse e f⟩,
    fun ⟨f⟩ ⟨g⟩ => ⟨compose e f g⟩⟩

@[expose] def RigidifiedClass := Quotient (compatibleSetoid e)

variable (p : X ⟶ S)

/-- Forgetting the actual trivialization descends through actual compatible
isomorphisms to the original relative quotient by base lines. -/
@[expose] def toRelative : RigidifiedClass e → RelativeClass p :=
  Quotient.lift (relativeClass p e) (by
    intro L M h
    obtain ⟨f⟩ := h
    exact congrArg (classMap p) (LineSheafClass318.classOf_eq f.iso))

@[simp] lemma toRelative_mk (L : RigidifiedLine e) :
    toRelative e p (Quotient.mk (compatibleSetoid e) L) = relativeClass p e L := rfl

lemma toRelative_surjective (hs : e ≫ p = 𝟙 S) : Function.Surjective (toRelative e p) := by
  intro c
  obtain ⟨L, hL⟩ := RigidifiedRelativeClass318.relativeClass_surjective p e hs c
  exact ⟨Quotient.mk (compatibleSetoid e) L, hL⟩

lemma toRelative_injective (hs : e ≫ p = 𝟙 S) (he : Function.Bijective e.appTop) :
    Function.Injective (toRelative e p) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro L M h
  exact Quotient.sound ((relative_eq_iff_compatible p e hs he L M).mp h)

/-- The quotient of actual rigidified objects by their actual compatible
isomorphisms is precisely the original relative quotient. This is not an
identification with every value of the associated fppf sheaf. -/
@[expose] def equivalence (hs : e ≫ p = 𝟙 S) (he : Function.Bijective e.appTop) :
    RigidifiedClass e ≃ RelativeClass p :=
  Equiv.ofBijective (toRelative e p)
    ⟨toRelative_injective e p hs he, toRelative_surjective e p hs⟩

/-- Choose one actual rigidified representative of each original relative class. -/
@[expose] def representative (hs : e ≫ p = 𝟙 S) (c : RelativeClass p) : RigidifiedLine e :=
  Classical.choose (RigidifiedRelativeClass318.relativeClass_surjective p e hs c)

lemma representative_class (hs : e ≫ p = 𝟙 S) (c : RelativeClass p) :
    relativeClass p e (representative e p hs c) = c :=
  Classical.choose_spec (RigidifiedRelativeClass318.relativeClass_surjective p e hs c)

/-- Every actual rigidified line is connected to the selected representative
by an actual compatible isomorphism. -/
@[expose] def representativeIso (hs : e ≫ p = 𝟙 S) (he : Function.Bijective e.appTop)
    (L : RigidifiedLine e) :
    CompatibleIso e L (representative e p hs (relativeClass p e L)) :=
  transition e p hs he (representative_class e p hs (relativeClass p e L)).symm

/-- Any two choices representing the same class agree by a unique actual
compatible isomorphism, so the choice has no unrecorded automorphism ambiguity. -/
lemma representatives_unique (hs : e ≫ p = 𝟙 S) (he : Function.Bijective e.appTop)
    (c : RelativeClass p) (L M : RigidifiedLine e)
    (hL : relativeClass p e L = c) (hM : relativeClass p e M = c) :
    ∃! _f : CompatibleIso e L M, True :=
  (relative_eq_iff_unique_compatible p e hs he L M).mp (hL.trans hM.symm)
end RigidifiedClassQuotient318
