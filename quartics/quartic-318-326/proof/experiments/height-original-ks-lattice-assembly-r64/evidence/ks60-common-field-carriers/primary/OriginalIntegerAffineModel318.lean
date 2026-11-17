module
public import IntegralScaledFourRootModel318
public import ContactKummerOrder318
public section
noncomputable section
namespace OriginalIntegerAffineModel318
open Polynomial
open scoped TensorProduct

/-- Specify the coefficientwise inclusion explicitly, rather than relying on
an inferred polynomial algebra structure or sending the parameter to a scalar. -/
@[expose] def rationalPolynomialAlgebra : Algebra ℤ[X] ℚ[X] :=
  (Polynomial.mapRingHom (Int.castRingHom ℚ)).toAlgebra
attribute [local instance] rationalPolynomialAlgebra

/-- The original four contact coordinates, before any primes are inverted. -/
@[expose] def contacts : Fin 4 → ℤ := ![0,32,76832,-343]

theorem contacts_cast (i : Fin 4) :
    (contacts i : ℚ) = LinearContactSquareclass318.contacts i := by
  fin_cases i <;> norm_num [contacts, LinearContactSquareclass318.contacts]

variable (c : Fin 4 → ℚˣ)

/-- Clearing a rational twist by the square of its positive denominator
preserves its original signed squareclass and leaves integral coefficients. -/
@[expose] def coefficient (i : Fin 4) : ℤ[X] :=
  C ((c i : ℚ).num * ((c i : ℚ).den : ℤ)) * (X - C (contacts i))

abbrev Order := FourRootOrder318.Order (coefficient c)

@[expose] def rootScale (i : Fin 4) : ℚ[X]ˣ :=
  Units.map (Polynomial.C : ℚ →+* ℚ[X]).toMonoidHom
    (Units.mk0 ((c i : ℚ).den : ℚ) (by exact_mod_cast (c i : ℚ).den_nz))

theorem rootScale_value (i : Fin 4) :
    (rootScale c i : ℚ[X]) = C ((c i : ℚ).den : ℚ) := rfl

theorem cleared_scalar (i : Fin 4) :
    (((c i : ℚ).num * ((c i : ℚ).den : ℤ) : ℤ) : ℚ) =
      (c i : ℚ) * ((c i : ℚ).den : ℚ)^2 := by
  have hd : ((c i : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (c i : ℚ).den_nz
  have hn : ((c i : ℚ).num : ℚ) = (c i : ℚ) * ((c i : ℚ).den : ℚ) :=
    (div_eq_iff hd).mp (c i : ℚ).num_div_den
  push_cast
  rw [hn]
  ring

/-- Exact comparison with the original rational polynomial, including the
signed twist, original contact and denominator-root scaling. -/
theorem coefficient_comparison (i : Fin 4) :
    algebraMap ℤ[X] ℚ[X] (coefficient c i) =
      ContactKummerOrder318.coefficient c i * (rootScale c i : ℚ[X])^2 := by
  change Polynomial.map (Int.castRingHom ℚ) (coefficient c i) = _
  simp only [coefficient, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]
  change C ((((c i : ℚ).num * ((c i : ℚ).den : ℤ) : ℤ) : ℚ)) *
    (X - C (contacts i : ℚ)) = _
  rw [cleared_scalar, contacts_cast, rootScale_value]
  simp only [ContactKummerOrder318.coefficient, map_mul, map_pow]
  ring

/-- The integral affine order exists over all of Spec Z, with constant
rank16 over the affine parameter line. This is not a smoothness claim. -/
theorem finite_free : Module.Finite ℤ[X] (Order c) ∧ Module.Free ℤ[X] (Order c) :=
  IntegralScaledFourRootModel318.finite_free (coefficient c)

theorem rank_sixteen : Module.finrank ℤ[X] (Order c) = 16 :=
  IntegralScaledFourRootModel318.rank_sixteen (coefficient c)

/-- Rational base change is the literal original affine four-root source,
not merely a curve with matching degree or the same abstract function field. -/
@[expose] def rationalFiber :
    ℚ[X] ⊗[ℤ[X]] Order c ≃ₐ[ℚ[X]] ContactKummerOrder318.SourceOrder c :=
  IntegralScaledFourRootModel318.genericFiber (coefficient c)
    (ContactKummerOrder318.coefficient c) (rootScale c) (coefficient_comparison c)

/-- The integral order embeds into the same original rational affine source.
This rules out vertical torsion or an unrelated generic component. -/
@[expose] def embedding : Order c →+* ContactKummerOrder318.SourceOrder c :=
  (rationalFiber c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order c →ₐ[ℤ[X]]
      ℚ[X] ⊗[ℤ[X]] Order c).toRingHom

theorem embedding_injective : Function.Injective (embedding c) := by
  letI : Module.Free ℤ[X] (Order c) := (finite_free c).2
  have hi : Function.Injective (algebraMap ℤ[X] ℚ[X]) := by
    intro p q h
    apply Polynomial.ext
    intro n
    have hn := congrArg (fun f : ℚ[X] => f.coeff n) h
    change (p.map (Int.castRingHom ℚ)).coeff n =
      (q.map (Int.castRingHom ℚ)).coeff n at hn
    simp only [Polynomial.coeff_map] at hn
    exact Int.cast_injective hn
  exact (rationalFiber c).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=ℤ[X]) (A:=ℚ[X]) (B:=Order c) hi)

theorem order_domain : IsDomain (Order c) := by
  letI : IsDomain (ContactKummerOrder318.SourceOrder c) := ContactKummerOrder318.source_domain c
  exact Function.Injective.isDomain (embedding c) (embedding_injective c)

end OriginalIntegerAffineModel318
