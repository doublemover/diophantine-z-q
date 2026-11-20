module
public import SelectedMultiplicationCoefficient318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318
open SelectedCompletedMultiplication318 WeierstrassCoefficientMap318

namespace SelectedCoefficientZeroTest318
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A B : R) (h : IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S
local notation "p" => structureMap A B
local notation "p₁" => structureMap (a A) (a B)
local notation "f" => coefficientMap (S:=S) A B
local notation "b" => Spec.map (CommRingCat.ofHom a)
local notation "h₁" => CompletedAdditionCoefficient318.mapped_discriminant (S:=S) A B h

/-- The entire actual coefficient fiber is Cartesian, so it both
preserves and reflects each actual lower-order zero equation on any
Scheme test, without a faithful-flatness assumption on that test. -/
theorem zero_test_iff (m : ℕ) {T : Scheme.{u}} (q : T ⟶ scheme (a A) (a B)) :
    q ≫ mul (a A) (a B) h₁ m = (q ≫ p₁) ≫ infinity (a A) (a B) ↔
      (q ≫ f) ≫ mul A B h m = ((q ≫ f) ≫ p) ≫ infinity A B := by
  have hl : (q ≫ mul (a A) (a B) h₁ m) ≫ f = (q ≫ f) ≫ mul A B h m := by
    rw [Category.assoc q (mul (a A) (a B) h₁ m) f,
      ←SelectedMultiplicationCoefficient318.naturality A B h m,←Category.assoc]
  have hr : ((q ≫ p₁) ≫ infinity (a A) (a B)) ≫ f = ((q ≫ f) ≫ p) ≫ infinity A B := by
    calc
      _ = (q ≫ p₁) ≫ (b ≫ infinity A B) := by
        rw [Category.assoc (q ≫ p₁) (infinity (a A) (a B)) f,coefficientMap_infinity]
      _ = _ := by
        rw [←Category.assoc (q ≫ p₁) b (infinity A B),Category.assoc q p₁ b,
          ←coefficientMap_base A B,←Category.assoc q f p]
  constructor
  · intro hz
    rw [←hl,←hr,hz]
  · intro hz
    apply (WeierstrassBaseChange318.coefficient_base_pullback (S:=S) A B).hom_ext
    · rw [hl,hr,hz]
    · simp only [Category.assoc,mul_base,infinity_section,Category.comp_id]

end SelectedCoefficientZeroTest318

#print axioms SelectedCoefficientZeroTest318.zero_test_iff
