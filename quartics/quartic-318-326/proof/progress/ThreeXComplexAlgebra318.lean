module
public import ThreeXScalingAlgebra318
public import AnalyticThreeSignPoints318
public section
noncomputable section
namespace ThreeXComplexAlgebra318
open Polynomial OpenJModel318 OpenJAffineScheme318 OpenJComplexEvaluation318
open scoped TensorProduct
set_option maxHeartbeats 0

instance complex_three : Invertible (3:ℂ) := invertibleOfNonzero (by norm_num)

lemma map_polynomial {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [Invertible (3:R)] [Invertible (3:K)] (A B : R) :
    (ShortThreeTorsion318.polynomial A B).map (algebraMap R K) =
      ShortThreeTorsion318.polynomial (algebraMap R K A) (algebraMap R K B) := by
  have he := congrArg (algebraMap R K) (mul_invOf_self (3:R))
  simp only [map_mul,map_ofNat,map_one] at he
  have hi : algebraMap R K (⅟ (3:R)) = ⅟ (3:K) := by
    rw [invOf_eq_inv]
    exact (inv_eq_of_mul_eq_one_right he).symm
  simp only [ShortThreeTorsion318.polynomial,Polynomial.map_sub,Polynomial.map_add,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,Polynomial.map_ofNat,
    map_mul,map_pow,map_ofNat,hi]

abbrev AnalyticRing (tau : UpperHalfPlane) :=
  ShortThreeTorsion318.Ring (ModularWeierstrass318.curve tau).a₄ (ModularWeierstrass318.curve tau).a₆

lemma actual_polynomial_map (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    (ShortThreeTorsion318.polynomial (A N) (B N)).map (algebraMap (Base N) ℂ) =
      ShortThreeTorsion318.polynomial (fiber N tau h).a₄ (fiber N tau h).a₆ := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  have ha : algebraMap (Base N) ℂ (A N)=(fiber N tau h).a₄ := rfl
  have hb : algebraMap (Base N) ℂ (B N)=(fiber N tau h).a₆ := rfl
  simpa only [ha,hb] using map_polynomial (K:=ℂ) (A N) (B N)

/-- Actual base change of the specified integral quartic algebra is
isomorphic to the actual analytic Weierstrass third-division algebra.
This strengthens the preceding complex-point bijection to a ring isomorphism. -/
@[expose] def xAlgebraEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ℂ ⊗[Base N] ThreeTorsionAlgebra318.XRing (A N) (B N) ≃ₐ[ℂ] AnalyticRing tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  let s : ℂˣ := Units.mk0 (CanonicalXScale318.scale (tau:ℂ)) (CanonicalXScale318.scale_ne_zero N tau h)
  have hc := CanonicalXScale318.coefficient_comparison N tau h
  exact (MonogenicSplitEquiv318.baseChange (S:=ℂ) (ShortThreeTorsion318.polynomial (A N) (B N))).trans
    ((AdjoinRoot.algEquivOfEq ℂ _ _ (actual_polynomial_map N tau h)).trans
      ((ThreeXScalingAlgebra318.algebraEquiv (fiber N tau h).a₄ (fiber N tau h).a₆ s).symm.trans
        (AdjoinRoot.algEquivOfEq ℂ _ _ (by
          change ShortThreeTorsion318.polynomial
            (CanonicalXScale318.scale (tau:ℂ)^2*(fiber N tau h).a₄)
            (CanonicalXScale318.scale (tau:ℂ)^3*(fiber N tau h).a₆)=_
          rw [←hc.1,←hc.2]))))

/-- The canonical full diamond fixed algebra has the same actual complex
base-changed algebra isomorphism, using the already-proved rank-four sign quotient. -/
@[expose] def fixedAlgebraEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ℂ ⊗[Base N] LiteralThreeXComparison318.Fixed N ≃ₐ[ℂ] AnalyticRing tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=ℂ) (A₁:=ℂ))
    (ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)).symm).trans
      (xAlgebraEquiv N tau h)

end ThreeXComplexAlgebra318
