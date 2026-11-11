module
public import ContactLiteralTripleFamilyCycle318
public section
noncomputable section
namespace ContactZeroTripleTransition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318

private lemma conjugate_cycle {C : Type*} [Category C] {X Y Z A B D : C}
    (e : X ≅ A) (f : Y ≅ B) (g : Z ≅ D) (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ A)
    (h : a ≫ b ≫ c=𝟙 A) :
    (e.hom ≫ a ≫ f.inv) ≫ (f.hom ≫ b ≫ g.inv) ≫ (g.hom ≫ c ≫ e.inv)=𝟙 X := by
  calc
    _ = e.hom ≫ (a ≫ b ≫ c) ≫ e.inv := by
      simp only [Category.assoc,Iso.inv_hom_id_assoc]
    _ = 𝟙 X := by rw [h]; simp only [Category.id_comp,Iso.hom_inv_id]

variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "e" => ContactLiteralTripleZeroFamily318.intersectionIso R c L hz
local notation "r" => ContactLiteralTripleFamilyRotation318.rotation R c L hz

/-- The triple transition now lives on the ACTUAL intersections of the
original zero-family overlaps. Its two comparisons retain the literal
triple scheme and the actual original finite-flat chart family. -/
@[expose] def transition (i j k : Fin F.size) : pullback (inc i j) (inc i k) ⟶
    pullback (inc j k) (inc j i) := (e i j k).hom ≫ r i j k ≫ (e j k i).inv

/-- Actual categorical triple cocycle on the geometric intersections,
not only on parameter points or on abstractly isomorphic total spaces.
The remaining gluing field is its exact pairwise-overlap leg equation. -/
lemma cycle (i j k : Fin F.size) :
    transition R c L hz i j k ≫ transition R c L hz j k i ≫ transition R c L hz k i j=𝟙 _ :=
  conjugate_cycle (e i j k) (e j k i) (e k i j) (r i j k) (r j k i) (r k i j)
    (ContactLiteralTripleFamilyCycle318.cycle R c L hz i j k)
end ContactZeroTripleTransition318
