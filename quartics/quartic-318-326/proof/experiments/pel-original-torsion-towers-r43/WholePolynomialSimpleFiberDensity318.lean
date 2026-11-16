module
public import FractionSeparablePolynomialOpen318
public import LocalizedMonicRootDensity318
public section
noncomputable section
namespace WholePolynomialSimpleFiberDensity318
open Polynomial Set
variable {ι : Type*} [Fintype ι]

/-- Generic separability of a WHOLE monic polynomial produces an actual
nonzero original base polynomial above which every full specialization
is separable. The specialized equation is the SAME original polynomial,
not a replacement chosen only after localization. -/
theorem exists_separable_open (Q : Polynomial (MvPolynomial ι ℂ)) (hm : Q.Monic)
    (hs : (Q.map (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)))).Separable) :
    ∃ d : MvPolynomial ι ℂ, d ≠ 0 ∧
      ∀ v : ι → ℂ, MvPolynomial.eval v d ≠ 0 → (Q.map (MvPolynomial.eval v)).Separable := by
  let R := MvPolynomial ι ℂ
  let K := FractionRing R
  obtain ⟨d,hd,P,A,B,hP,hPm,hPB⟩ := FractionSeparablePolynomialOpen318.exists_open R K
    (Q.map (algebraMap R K)) (hm.map _) hs
  have hsame : P = Q.map (algebraMap R (Localization.Away d)) := by
    ext k
    apply FractionFiniteCoefficientLift318.toField_injective R K d hd
    have h := congrArg (fun q : Polynomial K => q.coeff k) hP
    simpa only [Polynomial.coeff_map,FractionFiniteCoefficientLift318.toField_coefficient] using h
  refine ⟨d,hd,?_⟩
  intro v hv
  have hspec := (FractionSeparablePolynomialOpen318.specialize (R:=R) hPm hPB
    (ComplexPolynomialOpenPoints318.evaluation d v hv)).2.1
  have he : P.map (ComplexPolynomialOpenPoints318.evaluation d v hv) =
      Q.map (MvPolynomial.eval v) := by
    ext k
    simp only [hsame,Polynomial.coeff_map,ComplexPolynomialOpenPoints318.evaluation_source]
  rwa [he] at hspec

/-- The whole base has a genuinely Euclidean-dense locus of simple
fibers. This uses the polynomial identity principle for the produced
nonzero cutoff, not an asserted Zariski-to-Euclidean implication. -/
theorem dense_separable (Q : Polynomial (MvPolynomial ι ℂ)) (hm : Q.Monic)
    (hs : (Q.map (algebraMap (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)))).Separable) :
    Dense {v : ι → ℂ | (Q.map (MvPolynomial.eval v)).Separable} := by
  obtain ⟨d,hd,hsep⟩ := exists_separable_open Q hm hs
  exact (LocalizedMonicRootDensity318.polynomial_nonzero_dense d hd).mono hsep
end WholePolynomialSimpleFiberDensity318
