module
public import ContactBoundedDifferenceOriginalSheaf318
public section
noncomputable section
namespace ContactAffineRelativeClassPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
open ContactOriginalRelativePolynomialCharts318 RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- Every element of the ACTUAL naive relative line-class group at an
affine coefficient test has an fppf-local preimage under the original
bounded-divisor-difference Abel map. No representative is supplied by
the caller, and no injectivity of the unit is used. -/
theorem exists_presentation (x : RelativeLineClassBaseChange318.TestClass p (baseMap R)) :
    ∃ (T : Scheme.{0}) (t : T ⟶ Spec R),
      Flat t ∧ Surjective t ∧ LocallyOfFinitePresentation t ∧
      ∃ (N M : ℕ) (D : ContactBoundedCartierEquiv318.Data c N (t ≫ baseMap R))
        (E : ContactBoundedCartierEquiv318.Data c M (t ≫ baseMap R)),
        (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk (t ≫ baseMap R))) (⟨N,D⟩,⟨M,E⟩)=
          (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk t rfl).op (value p (baseMap R) x) := by
  obtain ⟨a,rfl⟩ := RelativeLineClassQuotient318.classMap_surjective (pullback.snd p (baseMap R)) x
  induction a using LineSheafClass318.induction with
  | h L => exact ContactBoundedDifferenceOriginalSheaf318.exists_presentation R c L
end ContactAffineRelativeClassPresentation318
