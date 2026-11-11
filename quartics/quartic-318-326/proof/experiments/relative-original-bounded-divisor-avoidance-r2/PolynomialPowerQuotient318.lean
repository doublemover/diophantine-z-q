module
public import PolynomialCoefficientWindow318
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Quotient.Basic
public section
noncomputable section
namespace PolynomialPowerQuotient318
open scoped BigOperators
set_option maxHeartbeats 800000
universe u
variable (R : Type u) [CommRing R] (r b : ℕ)

@[expose] def power : (Fin r → Polynomial R) →ₗ[R] (Fin r → Polynomial R) where
  toFun x := (Polynomial.X ^ (b+1) : Polynomial R) • x
  map_add' := smul_add _
  map_smul' := fun _ _ => smul_comm _ _ _

lemma encode_decode (x : Fin r → Fin (b+1) → R) :
    PolynomialCoefficientWindow318.encode R r b (PolynomialCoefficientWindow318.decode R r b x) = x := by
  ext i n
  change (∑ j : Fin (b+1), Polynomial.monomial j.val (x i j)).coeff n.val = x i n
  rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single n]
  · simp
  · intro j _ hj
    have hne : j.val ≠ n.val := by intro h; exact hj (Fin.ext h)
    simp [Polynomial.coeff_monomial,hne]
  · simp

lemma kernel : LinearMap.ker (PolynomialCoefficientWindow318.encode R r b) = (power R r b).range := by
  ext x
  constructor
  · intro hx
    have hz : ∀ i : Fin r, ∀ n < b+1, (x i).coeff n = 0 := by
      intro i n hn
      exact congrArg (fun z : Fin r → Fin (b+1) → R => z i ⟨n,hn⟩) hx
    choose y hy using fun i : Fin r => Polynomial.X_pow_dvd_iff.mpr (hz i)
    refine ⟨y,?_⟩
    ext i
    exact (hy i).symm
  · rintro ⟨y,rfl⟩
    ext i n
    have hd : (Polynomial.X ^ (b+1) : Polynomial R) ∣
        (Polynomial.X ^ (b+1) : Polynomial R) * y i := dvd_mul_right _ _
    exact Polynomial.X_pow_dvd_iff.mp hd n.val n.isLt

@[expose] def quotientMap : ((Fin r → Polynomial R) ⧸ (power R r b).range) →ₗ[R]
    (Fin r → Fin (b+1) → R) :=
  (power R r b).range.liftQ (PolynomialCoefficientWindow318.encode R r b) (by
    intro x hx
    exact (kernel R r b).symm ▸ hx)

lemma quotientMap_surjective : Function.Surjective (quotientMap R r b) := by
  intro x
  exact ⟨(power R r b).range.mkQ (PolynomialCoefficientWindow318.decode R r b x),encode_decode R r b x⟩

lemma quotientMap_injective : Function.Injective (quotientMap R r b) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  change z=0
  obtain ⟨x,rfl⟩ := (power R r b).range.mkQ_surjective z
  change PolynomialCoefficientWindow318.encode R r b x=0 at hz
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  have hx : x ∈ LinearMap.ker (PolynomialCoefficientWindow318.encode R r b) := hz
  rw [kernel] at hx
  exact hx

/-- The actual polynomial free module modulo X^(b+1), through its
literal coefficient map, is a finite FREE R-module. -/
@[expose] def equivalence : ((Fin r → Polynomial R) ⧸ (power R r b).range) ≃ₗ[R]
    (Fin r → Fin (b+1) → R) :=
  LinearEquiv.ofBijective (quotientMap R r b) ⟨quotientMap_injective R r b,quotientMap_surjective R r b⟩
end PolynomialPowerQuotient318
