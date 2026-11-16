module
public import PrueferBoundedCoordinates318
public section
noncomputable section
namespace BoundedCircleCharacters318
open PrueferBoundedCoordinates318 PrueferCanonicalTateTower318

/-- The literal subgroup carrier of Q/Z killed by 2^n. -/
def boundedCircle (n : ℕ) := {x : AddCircle (1 : ℚ) // (2^n) • x = 0}

/-- Bounded numerator coordinates enumerate every point of the actual
bounded torsion carrier; no finiteness of all Q/Z is assumed. -/
def encodeBounded (n : ℕ) (a : Fin (2^n)) : boundedCircle n :=
  ⟨encode n a.val, by
    change (2^n) • (a.val • circle n) = 0
    rw [smul_comm, circle_annihilated, nsmul_zero]⟩

theorem encodeBounded_surjective (n : ℕ) : Function.Surjective (encodeBounded n) := by
  intro x
  obtain ⟨a, ha, he⟩ := exists_bounded_coordinate n x.val x.property
  refine ⟨⟨a, ha⟩, ?_⟩
  exact Subtype.ext he

instance boundedCircle_finite (n : ℕ) : Finite (boundedCircle n) :=
  Finite.of_surjective (encodeBounded n) (encodeBounded_surjective n)

/-- A character on a bounded-exponent group takes values in the actual
finite torsion subgroup, rather than arbitrary elements of Q/Z. -/
def characterValues {G : Type*} [AddCommGroup G] (n : ℕ)
    (hG : ∀ x : G, (2^n) • x = 0) :
    (G →+ AddCircle (1 : ℚ)) → (G → boundedCircle n) :=
  fun f x => ⟨f x, by rw [← map_nsmul, hG x, map_zero]⟩

theorem characterValues_injective {G : Type*} [AddCommGroup G] (n : ℕ)
    (hG : ∀ x : G, (2^n) • x = 0) : Function.Injective (characterValues n hG) := by
  intro f g h
  apply AddMonoidHom.ext
  intro x
  exact congrArg Subtype.val (congrFun h x)

/-- Characters of a finite bounded-exponent group form a finite group.
The proof controls both the domain and the values of every character. -/
theorem finite_characters {G : Type*} [AddCommGroup G] [Finite G] (n : ℕ)
    (hG : ∀ x : G, (2^n) • x = 0) : Finite (G →+ AddCircle (1 : ℚ)) :=
  Finite.of_injective (characterValues n hG) (characterValues_injective n hG)

end BoundedCircleCharacters318
