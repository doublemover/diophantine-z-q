module
public import LocalizedMonicPolynomialDescent318
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace MonicGrowthIntegralFraction318
open Polynomial ComplexPolynomialOpenPoints318
abbrev Base := MvPolynomial (Fin 2) ℂ
variable {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- A root of the SAME localized monic equation is integral over the
WHOLE original algebra once all its coefficients have denominator-free
polynomial growth. The full coefficient-map square is retained. -/
theorem isIntegral (d : Base) (hd : d ≠ 0)
    (g : Base →+* A) (φ : Localization.Away d →+* K)
    (hφ : φ.comp (algebraMap Base (Localization.Away d)) = (algebraMap A K).comp g)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (y : K) (hy : Q.eval₂ φ y = 0)
    (hb : ∀ n, ∃ N C, 0 ≤ C ∧ ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      ‖evaluation d v hv (Q.coeff n)‖ ≤ C * (1+‖v‖)^N) : IsIntegral A y := by
  obtain ⟨P,hP,hPQ⟩ := LocalizedMonicPolynomialDescent318.exists_monic d hd Q hm hb
  refine ⟨P.map g,hP.map g,?_⟩
  rw [Polynomial.aeval_def,Polynomial.eval₂_map,←hφ,←Polynomial.eval₂_map,hPQ]
  exact hy

/-- The final regularity step uses normality of the ACTUAL whole ring,
not a different normal model or a presumed holomorphic GAGA principle. -/
theorem exists_regular [IsDomain A] [IsIntegrallyClosed A]
    (d : Base) (hd : d ≠ 0)
    (g : Base →+* A) (φ : Localization.Away d →+* FractionRing A)
    (hφ : φ.comp (algebraMap Base (Localization.Away d)) =
      (algebraMap A (FractionRing A)).comp g)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (y : FractionRing A) (hy : Q.eval₂ φ y = 0)
    (hb : ∀ n, ∃ N C, 0 ≤ C ∧ ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      ‖evaluation d v hv (Q.coeff n)‖ ≤ C * (1+‖v‖)^N) :
    ∃ a : A, algebraMap A (FractionRing A) a = y := by
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (isIntegral d hd g φ hφ Q hm y hy hb)
end MonicGrowthIntegralFraction318
