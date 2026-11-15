module
public import RelativeFppfCoefficientEquality318
public section
noncomputable section
namespace ContactBoundedDifferenceOriginalSheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
open ContactOriginalRelativePolynomialCharts318 RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- Genuine fppf-local divisor-difference presentation in the SAME
original over-Q sheaf used by the moduli Abel morphism. The prior
coefficient-relative presentation is transported through a constructed
map of the actual associated sheaves. -/
theorem exists_presentation : ∃ (T : Scheme.{0}) (t : T ⟶ Spec R),
    Flat t ∧ Surjective t ∧ LocallyOfFinitePresentation t ∧
    ∃ (N M : ℕ) (D : ContactBoundedCartierEquiv318.Data c N (t ≫ baseMap R))
      (E : ContactBoundedCartierEquiv318.Data c M (t ≫ baseMap R)),
      (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk (t ≫ baseMap R))) (⟨N,D⟩,⟨M,E⟩)=
        (RelativeFppfLineSheaf318.sheaf p).obj.map (Over.homMk t rfl).op
          (value p (baseMap R) (RelativeLineClassQuotient318.classMap (pullback.snd p (baseMap R)) (classOf L))) := by
  obtain ⟨T,t,hf,hs,hp,N,M,D,E,h⟩ := ContactPositiveDifferencePresentation318.exists_bounded_difference R c L
  refine ⟨T,t,hf,hs,hp,N,M,D,E,?_⟩
  have he := RelativeFppfCoefficientEquality318.transport p (baseMap R) t
    (ContactCartierDifferenceLine318.line c N M (t ≫ baseMap R) D E) (classOf L) h
  exact (ContactCartierDifferenceLine318.value c N M (t ≫ baseMap R) D E).symm.trans he
end ContactBoundedDifferenceOriginalSheaf318
