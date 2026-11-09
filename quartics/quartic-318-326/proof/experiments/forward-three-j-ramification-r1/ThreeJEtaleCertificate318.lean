module
public import ThreeJFullLocalDegree318
public import Mathlib.RingTheory.Etale.StandardEtale
public section
noncomputable section
namespace ThreeJEtaleCertificate318
open Polynomial ThreeJMonicAlgebra318
set_option maxHeartbeats 2000000

@[expose] def branchPolynomial : Base := X*(X-1728)
@[expose] def bezoutA : Polynomial Base :=
  C (-8*X^3+13068*X^2+1306368*X)*X^3+
  C (8*X^4-18873*X^3+8284356*X^2+760866048*X)*X^2+
  C (-243*X^4-1102248*X^3+2561545620*X^2+118770686208*X)*X+
  C (-86093442*X^3+147219785820*X^2+2677850419968*X)
@[expose] def bezoutB : Polynomial Base :=
  C (32*X^3-52272*X^2-5225472*X)*X^2+
  C (-24*X^4+56376*X^3-24564384*X^2-2055849984*X)*X+
  C (729*X^4+1732104*X^3-5093330544*X^2-132239526912*X)

/-- Exact polynomial Bezout identity for the original universal quartic
and its derivative. It supplies a scheme-level standard-etale certificate. -/
lemma integer_bezout : polynomial.derivative*bezoutA+polynomial*bezoutB=
    (3:Polynomial Base)^24*(C branchPolynomial)^2 := by
  simp only [polynomial,bezoutA,bezoutB,branchPolynomial,derivative_add,
    derivative_mul,derivative_pow,derivative_X,derivative_C,map_add,map_sub,
    map_mul,map_pow,map_neg,map_ofNat,mul_zero,zero_mul,zero_add,add_zero]
  ring

@[expose] def scalar : Polynomial Base := algebraMap ℚ (Polynomial Base) (1/3^24)
lemma scalar_identity : (3:Polynomial Base)^24*scalar=1 := by
  have h : (3:ℚ)^24*(1/3^24)=1 := by norm_num
  simpa only [map_mul,map_pow,map_ofNat,map_one,scalar] using
    congrArg (algebraMap ℚ (Polynomial Base)) h

/-- The localization is away from the actual coefficient j(j-1728), not
an unspecified derivative open. -/
@[expose] def pair : StandardEtalePair Base where
  f := polynomial
  monic_f := monic
  g := C branchPolynomial
  cond := ⟨bezoutA*scalar,bezoutB*scalar,2,by
    linear_combination integer_bezout*scalar-(C branchPolynomial)^2*scalar_identity⟩
abbrev LocalModel := Localization.Away (AdjoinRoot.mk polynomial (C branchPolynomial))
lemma local_model_etale : Algebra.Etale Base LocalModel :=
  Algebra.Etale.of_equiv pair.equivAwayAdjoinRoot

end ThreeJEtaleCertificate318
