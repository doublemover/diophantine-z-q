module
public import ActualPrimitivePrimePower318
public section
noncomputable section
namespace ActualPrescribedPrimePower318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualPrimitiveResidueLiftSet318
open ActualPrimitivePrimePower318
set_option maxHeartbeats 26000000

/-- The literal successive ambient moduli, with no coprime-CRT step. -/
@[expose] def modulus (m p : ℕ) : ℕ → ℕ
  | 0 => m
  | e+1 => modulus m p e*p
lemma modulus_eq (m p e : ℕ) : modulus m p e=m*p^e := by
  induction e with
  | zero => simp only [modulus,pow_zero,mul_one]
  | succ e ih => simp only [modulus,ih,pow_succ,mul_assoc]
instance modulusNeZero (m p e : ℕ) [NeZero m] [NeZero p] : NeZero (modulus m p e) := by
  rw [modulus_eq]
  infer_instance
lemma prime_dvd_modulus (m p e : ℕ) (hpm : p∣m) : p∣modulus m p e := by
  rw [modulus_eq]
  exact hpm.trans (dvd_mul_right m (p^e))

/-- Every later set is the FULL original ambient preimage of the
previous set. Hence these are actual compatible congruence conditions,
not abstract sets chosen to have the desired cardinalities. -/
@[expose] def levels (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (R : Finset (Quadric (κ:ZMod m))) :
    (e : ℕ) → Finset (Quadric (κ:ZMod (modulus m p e)))
  | 0 => R
  | e+1 => by
    classical
    exact Finset.univ.filter (fun y => reduceQuadric κ (modulus m p e) p y∈levels κ m p R e)

lemma mem_next_level (κ : ℤ) (m p e : ℕ) [NeZero m] [NeZero p]
    (R : Finset (Quadric (κ:ZMod m)))
    (y : Quadric (κ:ZMod (modulus m p (e+1)))) :
    y∈levels κ m p R (e+1) ↔
      reduceQuadric κ (modulus m p e) p y∈levels κ m p R e := by
  classical
  simp only [levels,Finset.mem_filter,Finset.mem_univ,true_and]

/-- No singular residue is introduced by any of these actual lifts. -/
theorem all_levels_primitive (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hpm : p∣m) (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,IsPrimitive κ m p x) (e : ℕ) :
    ∀x∈levels κ m p R e,IsPrimitive κ (modulus m p e) p x := by
  induction e with
  | zero => exact hR
  | succ e ih =>
    intro x hx
    have hx' := (mem_next_level κ m p e R x).mp hx
    exact actual_lift_preserves_primitivity κ (modulus m p e) p
      (prime_dvd_modulus m p e hpm) (levels κ m p R e) ih ⟨x,hx'⟩

lemma next_level_card (κ : ℤ) (m p e : ℕ) [NeZero m] [NeZero p]
    (R : Finset (Quadric (κ:ZMod m))) :
    (levels κ m p R (e+1)).card=
      Nat.card (LiftSet κ (modulus m p e) p (levels κ m p R e)) := by
  classical
  change (Finset.univ.filter (fun y => reduceQuadric κ (modulus m p e) p y∈levels κ m p R e)).card=_
  unfold LiftSet
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Exact cardinality of EVERY iterated original congruence preimage,
including empty subsets and arbitrary original starting prime power. -/
theorem actual_prescribed_prime_power_count (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m)
    (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,IsPrimitive κ m p x) (e : ℕ) :
    (levels κ m p R e).card=R.card*(p^4)^e := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  induction e with
  | zero => simp only [levels,pow_zero,mul_one]
  | succ e ih =>
    rw [next_level_card,actual_primitive_subset_lift_count κ (modulus m p e) p hp hp2 hκ
      (prime_dvd_modulus m p e hpm) _ (all_levels_primitive κ m p hpm R hR e),ih,pow_succ (p^4) e]
    exact mul_assoc _ _ _

end ActualPrescribedPrimePower318
