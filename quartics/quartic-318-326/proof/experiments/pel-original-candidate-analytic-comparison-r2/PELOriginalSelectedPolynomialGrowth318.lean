module
public import PELOriginalGlobalSelectedPolynomial318
public import LocalizedSelectedPolynomialGrowth318
public section
noncomputable section
namespace PELOriginalSelectedPolynomialGrowth318
open Polynomial QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The original selected coefficients satisfy the genuine common pole
bound needed by the global polynomial-numerator argument, on the SAME
produced base open and with uniform exponents for every coefficient. -/
theorem exists_growth (hm : Q.Monic) (hs : Q.Separable) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : ComplexVectors, MvPolynomial.eval v d ≠ 0 → ∀ n : ℕ,
        ‖MvPolynomial.eval v d ^ M *
          (PELOriginalGlobalSelectedPolynomial318.selectedPolynomial τ hτ j x d Q e he hm v).coeff n‖ ≤
            C*(1+‖v‖)^N :=
  LocalizedSelectedPolynomialGrowth318.exists_selected_growth d Q hm hs
    (Set.range (originalOpenRootPoint τ hτ j x d Q e he))
end PELOriginalSelectedPolynomialGrowth318
