module
public import RationalPointBox318
public import PrimitiveQuadratic318
public import QuadraticHeightBounds
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public section
noncomputable section
namespace HeightCoverageFromMahler318
open Polynomial ConcreteG8Domain PolynomialHeightInterface318

@[expose] def quadratic (a : ℕ) (b c : ℤ) : ℤ[X] := C (a:ℤ)*X^2+C b*X+C c

/-- The one remaining number-field theorem. This predicate is NOT proved here.
All primitive-polynomial existence, discriminant, finite coefficient and
rational-point consequences are supplied by the checked modules. -/
@[expose] def PrimitiveHeightIdentity : Prop :=
  ∀ (u v : ℚ), v≠0 → ∀ (a : ℕ) (b c : ℤ), 1≤a →
    Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1 →
    (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 →
    ((quadratic a b c).map (Int.castRingHom ℂ)).mahlerMeasure =
      Real.exp (2*NumberField.absLogHeight₁ (pair u v))

lemma nonrational_box_of_height_identity (heightIdentity : PrimitiveHeightIdentity)
    (u v : ℚ) (hv : v≠0) (hx : NumberField.absLogHeight₁ (pair u v)<Real.log 9) :
    PolynomialBox u v := by
  obtain ⟨a,b,c,k,ha,hk,hprim,hp,hd⟩ :=
    PrimitiveQuadratic318.primitive_defining_quadratic_discriminant u v hv
  have hdeg : (quadratic a b c).natDegree=2 :=
    Polynomial.natDegree_quadratic (by omega : (a:ℤ)≠0)
  have hM := QuadraticHeightBounds.mahler_lt_of_actual_height (pair u v) (quadratic a b c)
    (heightIdentity u v hv a b c ha hprim hp) hx
  obtain ⟨hA,hB,hC⟩ := QuadraticHeightBounds.quadratic_coeff_bounds (quadratic a b c) hdeg hM
  simp only [quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] at hA hB hC
  norm_num at hA hB hC
  have hA' : a≤81 := by exact_mod_cast hA
  have hK := QuadraticHeightBounds.discriminant_bound (a:ℤ) b c k (by omega) (by omega) hB hC hd
  have hC' : c.natAbs≤81 := by
    exact_mod_cast (show (c.natAbs:ℤ)≤81 by simpa only [Int.natCast_natAbs] using hC)
  have hb := abs_le.mp hB
  exact Or.inr ⟨hv,a,b,c,k,ha,hA',hb.1,hb.2,hC',hk,hK,hprim,hp,hd⟩

/-- The user's actual global coverage, with exactly the remaining
primitive-Mahler/absolute-height theorem visible as an argument. -/
theorem polynomial_height_coverage_of_height_identity (heightIdentity : PrimitiveHeightIdentity) :
    PolynomialHeightCoverage :=
  RationalPointBox318.coverage_of_nonrational (nonrational_box_of_height_identity heightIdentity)

#print axioms nonrational_box_of_height_identity
#print axioms polynomial_height_coverage_of_height_identity
end HeightCoverageFromMahler318
