module
public import PolynomialPowerQuotient318
public import QuotientProjectiveRetract318
public import Mathlib.RingTheory.Finiteness.Projective
public section
noncomputable section
namespace PolynomialProjectiveJet318
set_option maxHeartbeats 750000
universe u v
variable (R : Type u) [CommRing R] (N : Type v) [AddCommGroup N]
  [Module (Polynomial R) N] [Module R N] [IsScalarTower R (Polynomial R) N]
  [Module.Finite (Polynomial R) N] [Module.Projective (Polynomial R) N]

@[expose] def power (b : ℕ) : N →ₗ[R] N where
  toFun x := (Polynomial.X ^ (b+1) : Polynomial R) • x
  map_add' := smul_add _
  map_smul' := fun _ _ => smul_comm _ _ _

/-- Jets of an ACTUAL finite projective polynomial module are finite
projective over the coefficient ring, including nonreduced bases. -/
theorem finite_projective (b : ℕ) :
    Module.Finite R (N ⧸ (power R N b).range) ∧ Module.Projective R (N ⧸ (power R N b).range) := by
  obtain ⟨r,back,out,_,_,h⟩ := Module.Finite.exists_comp_eq_id_of_projective (Polynomial R) N
  letI : Module.Finite R ((Fin r → Polynomial R) ⧸ (PolynomialPowerQuotient318.power R r b).range) :=
    Module.Finite.equiv (PolynomialPowerQuotient318.equivalence R r b).symm
  letI : Module.Projective R ((Fin r → Polynomial R) ⧸ (PolynomialPowerQuotient318.power R r b).range) :=
    Module.Projective.of_equiv (PolynomialPowerQuotient318.equivalence R r b).symm
  exact QuotientProjectiveRetract318.finite_projective
    (out.restrictScalars R) (back.restrictScalars R)
    (by ext x; exact LinearMap.congr_fun h x)
    (power R N b) (PolynomialPowerQuotient318.power R r b)
    (by ext x; exact out.map_smul (Polynomial.X ^ (b+1)) x)
    (by ext x; exact back.map_smul (Polynomial.X ^ (b+1)) x)
/-- Polynomial multiplication by a coordinate power is injective on the
actual projective module, even with nilpotent coefficient elements. -/
theorem power_injective (b : ℕ) : Function.Injective (power R N b) := by
  obtain ⟨r,back,out,_,hout,h⟩ := Module.Finite.exists_comp_eq_id_of_projective (Polynomial R) N
  intro x y hxy
  apply hout
  ext i
  have he := congrArg (fun z : N => out z i) hxy
  change out ((Polynomial.X ^ (b+1) : Polynomial R) • x) i =
    out ((Polynomial.X ^ (b+1) : Polynomial R) • y) i at he
  rw [out.map_smul,out.map_smul] at he
  change (Polynomial.X ^ (b+1) : Polynomial R) * out x i =
    (Polynomial.X ^ (b+1) : Polynomial R) * out y i at he
  apply Polynomial.toLaurent_injective
  have hl := congrArg (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) he
  rw [map_mul,map_mul,Polynomial.toLaurent_X_pow] at hl
  have hc := congrArg (fun z : LaurentPolynomial R => LaurentPolynomial.T (-((b+1 : ℕ) : ℤ))*z) hl
  simpa only [← mul_assoc,← LaurentPolynomial.T_add,neg_add_cancel,
    LaurentPolynomial.T_zero,one_mul] using hc
end PolynomialProjectiveJet318
