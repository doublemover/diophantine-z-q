module
public import OriginalR47GlobalCentreRees318
public import Mathlib.AlgebraicGeometry.FunctionField
import all OriginalR47IsolatedAffineCentres318
public section
noncomputable section

namespace OriginalR47ActualArithmeticTermination318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47IsolatedCentreCover318 (Centre off)
open OriginalR47GlobalCentreRees318 (proj unchanged)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
local notation "S" => Spec (CommRingCat.of R)

/-- The original whole-generic read. This is the unchanged predicate
from the arithmetic termination source, extracted before the recursive
normal-crossings atlas and still using its exact declared name. -/
abbrev GenericRead {Y X : Scheme.{u}} (s : X ⟶ S) (r : Y ⟶ X) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X), (∀ t, s (g t) = genericPoint S) →
    ∃ k : T ⟶ Y, IsPullback k (𝟙 T) r g

/-- Every generic-base map factors through the entire *actual* old
complement and the same global Rees round, by the strict Cartesian
complement. Thus the whole generic fibre, not just a mark value, is
preserved with both named arrows. -/
theorem generic_round {X : Scheme.{u}} (s : X ⟶ S)
    (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (pick : ∀ z : Z, Centre Z z) (vertical : ∀ z ∈ Z, s z ≠ genericPoint S) :
    GenericRead s (proj Z hZ hC pick) := by
  intro T g hg
  let V := off Z hZ hC
  have hRange : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨t,rfl⟩
    have ht : g t ∈ V := by
      change g t ∈ off Z hZ hC
      unfold off
      exact fun hz => vertical (g t) hz (hg t)
    exact ⟨⟨g t,ht⟩,Scheme.Opens.ι_apply V _⟩
  let a := IsOpenImmersion.lift V.ι g hRange
  have ha : a ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k,H⟩ := unchanged Z hZ hC pick
  have L : IsPullback a (𝟙 T) (𝟙 V.toScheme) a := IsPullback.of_id_snd
  refine ⟨a ≫ k,?_⟩
  simpa only [Category.comp_id,ha] using L.paste_horiz H

end OriginalR47ActualArithmeticTermination318

#print axioms OriginalR47ActualArithmeticTermination318.GenericRead
#print axioms OriginalR47ActualArithmeticTermination318.generic_round
