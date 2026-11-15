module
public import PELOriginalPrimitiveSeparableOpen318
public import AdjoinRootSeparablePointCount318
public import ComplexPolynomialOpenPoints318
public section
noncomputable section
namespace PELOriginalPrimitiveComplexFibers318
open Polynomial AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedGenericFinite318 PELOriginalPrimitiveSeparableOpen318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalCandidateAffineCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Produce the original primitive polynomial open and count its
actual base-preserving complex-valued MONOGENIC-order points exactly.
The count is the original generic field degree, and every root is
simple. Identification with the whole candidate chart still requires
the independently constructed actual localized-order isomorphism. -/
theorem produced_primitive_fibers (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : PolynomialBase, ∃ hd : d ≠ 0,
    ∃ Q A B : Polynomial (Localization.Away d),
      Q.map (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd) =
        rationalEquation τ hτ j x hx ∧
      Q.Monic ∧ A*Q+B*Q.derivative = 1 ∧
      ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0),
        Nat.card (AdjoinRootSpecializedPoints318.SchemePoints Q
          (ComplexPolynomialOpenPoints318.evaluation d v hv)) =
          Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j) ∧
        (∀ e : AdjoinRootSpecializedPoints318.Points Q
            (ComplexPolynomialOpenPoints318.evaluation d v hv),
          (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).derivative.eval
            (e.1 (AdjoinRoot.root Q)) ≠ 0) ∧
        (∀ q : AdjoinRootSpecializedPoints318.SchemePoints Q
            (ComplexPolynomialOpenPoints318.evaluation d v hv),
          q.1 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjoinRoot Q))) = 𝟙 _) := by
  obtain ⟨d,hd,Q,A,B,hQ,hm,hAB,hdeg⟩ := exists_separable_open τ hτ j x hx
  have hs : Q.Separable := (Polynomial.separable_def' Q).mpr ⟨A,B,hAB⟩
  refine ⟨d,hd,Q,A,B,hQ,hm,hAB,?_⟩
  intro v hv
  exact ⟨(AdjoinRootSeparablePointCount318.point_count Q
      (ComplexPolynomialOpenPoints318.evaluation d v hv) hm hs).trans hdeg,
    AdjoinRootSeparablePointCount318.every_point_simple Q
      (ComplexPolynomialOpenPoints318.evaluation d v hv) hs,
    AdjoinRootSpecializedPoints318.over_complex Q
      (ComplexPolynomialOpenPoints318.evaluation d v hv)
      (ComplexPolynomialOpenPoints318.evaluation_constant d v hv)⟩
end PELOriginalPrimitiveComplexFibers318
