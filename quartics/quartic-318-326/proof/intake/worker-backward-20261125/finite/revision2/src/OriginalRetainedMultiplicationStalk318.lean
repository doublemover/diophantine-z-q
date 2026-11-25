module

public import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Ring

@[expose] public section

namespace OriginalRetainedMultiplicationStalk318

variable {R : Type*} [CommRing R]
variable (I : Ideal R) (f : R→+*R) (n : R)
variable (residue : ∀ x : R, f x-x∈I)
variable (linear : ∀ x∈I, f x-n*x∈I^2)

include residue linear in
/-- On the actual identity-local ring a residue-identity map acting
as the integer n on the cotangent space acts as n^k on each old
ideal-power layer. No choice of complete regular parameters is used. -/
theorem power_layer (k : ℕ) (x : R) (hx : x∈I^k) :
    f x-n^k*x∈I^(k+1) := by
  induction k generalizing x with
  | zero =>
      simpa only [pow_zero,one_mul,Nat.zero_add,pow_one] using residue x
  | succ k ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro u hu v hv
        have ev : f v∈I := (sub_add_cancel (f v) v) ▸ I.add_mem (residue v) hv
        have a : (f u-n^k*u)*f v∈I^(k+1+1) := by
          rw [pow_succ]
          exact Ideal.mul_mem_mul (ih u hu) ev
        have b : (n^k*u)*(f v-n*v)∈I^(k+1+1) := by
          change (n^k*u)*(f v-n*v)∈I^(k+2)
          rw [pow_add]
          exact Ideal.mul_mem_mul ((I^k).mul_mem_left _ hu) (linear v hv)
        change f (u*v)-n^(k+1)*(u*v)∈I^(k+1+1)
        rw [map_mul]
        have e : f u*f v-n^(k+1)*(u*v) =
            (f u-n^k*u)*f v+(n^k*u)*(f v-n*v) := by
          rw [pow_succ]
          ring
        rw [e]
        exact (I^(k+1+1)).add_mem a b
      · intro u v hu hv
        rw [map_add,mul_add,add_sub_add_comm]
        exact (I^(k+1+1)).add_mem hu hv

include residue linear in
/-- Native local kernel elimination for the literal [n] stalk map.
Krull intersection replaces a completion/formal-power-series API. -/
theorem injective_from_cotangent_unit [IsNoetherianRing R] [IsLocalRing R]
    (proper : I≠⊤) (nunit : IsUnit n) : Function.Injective f := by
  have kill (x : R) (hx : f x=0) : x=0 := by
    have every (k : ℕ) : x∈I^k := by
      induction k with
      | zero =>
          rw [pow_zero,Ideal.one_eq_top]
          exact Submodule.mem_top
      | succ k ih =>
          have e := power_layer I f n residue linear k x ih
          rw [hx,zero_sub] at e
          exact ((I^(k+1)).unit_mul_mem_iff_mem (nunit.pow k)).1 ((I^(k+1)).neg_mem_iff.1 e)
    have inter : x∈(⨅ k : ℕ,I^k) := Ideal.mem_iInf.2 every
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I proper] at inter
    exact (Submodule.mem_bot R).1 inter
  intro u v e
  apply sub_eq_zero.1
  apply kill
  rw [map_sub,e,sub_self]

end OriginalRetainedMultiplicationStalk318
