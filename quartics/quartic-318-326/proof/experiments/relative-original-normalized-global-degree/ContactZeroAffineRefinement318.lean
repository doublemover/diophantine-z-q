module
public import SectionZeroAffineRefinement318
public import ContactGlobalZeroClosed318
public import ContactHZeroGeometricUnit318
public section
noncomputable section
namespace ContactZeroAffineRefinement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open SectionZeroAffineRefinement318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))
local notation "p" => ContactGlobalSectionZero318.into R c L s
local notation "A" => CommRingCat.of (R ⊗[ℚ] finiteRing c)
local notation "B" => CommRingCat.of (R ⊗[ℚ] infinityRing c)

lemma finite_ideal : finiteIdeal R c L s=sectionIdeal A (finiteInto R c) L s := by
  unfold finiteIdeal finiteSection
  rw [ContactHZeroGeometricUnit318.finite_pair]
  rfl
lemma infinity_ideal : infinityIdeal R c L s=sectionIdeal B (infinityInto R c) L s := by
  unfold infinityIdeal infinitySection
  rw [ContactHZeroGeometricUnit318.infinity_pair]
  rfl

/-- The ORIGINAL global zero chart, typed with the ideal of the actual
geometric section pullback rather than a separately named Cech component. -/
@[expose] def finiteChart : Spec (CommRingCat.of (A⧸sectionIdeal A (finiteInto R c) L s)) ⟶
    ContactGlobalSectionZero318.scheme R c L s :=
  transportInto A (finite_ideal R c L s) (ContactGlobalSectionZero318.finiteChart R c L s)

@[expose] def infinityChart : Spec (CommRingCat.of (B⧸sectionIdeal B (infinityInto R c) L s)) ⟶
    ContactGlobalSectionZero318.scheme R c L s :=
  transportInto B (infinity_ideal R c L s) (ContactGlobalSectionZero318.infinityChart R c L s)

lemma finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal A (finiteInto R c) L s))))
    (finiteChart R c L s) (finiteInto R c) p :=
  transport_square A (finiteInto R c) p (finite_ideal R c L s)
    (ContactGlobalSectionZero318.finiteChart R c L s)
    (ContactGlobalZeroChartSquares318.finite_square R c L s)

lemma infinity_square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sectionIdeal B (infinityInto R c) L s))))
    (infinityChart R c L s) (infinityInto R c) p :=
  transport_square B (infinityInto R c) p (infinity_ideal R c L s)
    (ContactGlobalSectionZero318.infinityChart R c L s)
    (ContactGlobalZeroChartSquares318.infinity_square R c L s)

variable (C : CommRingCat.{0})
/-- Every literal affine ring refinement of the finite chart is already
the exact zero quotient of its own genuine global-section pullback. -/
lemma finite_refinement (f : A ⟶ C) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (sectionIdeal C (Spec.map f ≫ finiteInto R c) L s))))
    (SectionZeroAffineRefinement318.into A C (finiteInto R c) f L s (finiteChart R c L s))
    (Spec.map f ≫ finiteInto R c) p :=
  SectionZeroAffineRefinement318.square A C (finiteInto R c) f L s p
    (finiteChart R c L s) (finite_square R c L s)
/-- Same original-model producer on every infinity-chart refinement. -/
lemma infinity_refinement (f : B ⟶ C) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (sectionIdeal C (Spec.map f ≫ infinityInto R c) L s))))
    (SectionZeroAffineRefinement318.into B C (infinityInto R c) f L s (infinityChart R c L s))
    (Spec.map f ≫ infinityInto R c) p :=
  SectionZeroAffineRefinement318.square B C (infinityInto R c) f L s p
    (infinityChart R c L s) (infinity_square R c L s)
end ContactZeroAffineRefinement318
