module
public import PELOriginalGlobalSelectedPolynomial318
public import LocalizedSelectedComplementProduct318
public section
noncomputable section
namespace PELOriginalSelectedComplementProduct318
open Polynomial QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The original selected polynomial and its actual candidate-root
complement multiply to the exact original candidate equation at EVERY
base point on D(d). No degree, positivity or rational-factor assertion
is substituted for the full polynomial identity. -/
theorem selected_mul_complement (hm : Q.Monic) (hs : Q.Separable)
    (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0) :
    PELOriginalGlobalSelectedPolynomial318.selectedPolynomial τ hτ j x d Q e he hm v *
      LocalizedPrimitiveSelectedPolynomial318.selectedPolynomial d Q hm
        (Set.range (originalOpenRootPoint τ hτ j x d Q e he))ᶜ v =
      Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv) :=
  LocalizedSelectedComplementProduct318.selected_mul_complement d Q hm hs _ v hv

/-- A proved trivial complement yields an actual original source point
for every independent root, via the exact original selected-range identity. -/
theorem original_point_of_complement_eq_one (hm : Q.Monic) (q : OpenRoots d Q)
    (hcomp : LocalizedPrimitiveSelectedPolynomial318.selectedPolynomial d Q hm
      (Set.range (originalOpenRootPoint τ hτ j x d Q e he))ᶜ q.val.val.1 = 1) :
    ∃ z, originalOpenRootPoint τ hτ j x d Q e he z = q :=
  LocalizedSelectedComplementProduct318.selected_of_complement_eq_one d Q hm _ q hcomp
end PELOriginalSelectedComplementProduct318
