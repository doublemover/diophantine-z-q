module
public import ActualTwoDescentSignReciprocity318
public section
noncomputable section
namespace ActualTwoDescentSupportParity318
open ActualTwoDescentSignReciprocity318 ZMod
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma sign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sign (∑ i ∈ s, f i)=∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,sign_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,sign_add,ih]

/-- The parity coordinate used in reciprocity is the actual symbol of -1. -/
lemma actual_minus_symbol (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (if jacobiSym (-1) p= -1 then 1 else 0 : ZMod 2)=((p/2 : ℕ) : ZMod 2) := by
  have hodd : p % 2=1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp2
  have hs : jacobiSym (-1) p=sign ((p/2 : ℕ) : ZMod 2) := by
    rw [←legendreSym.to_jacobiSym,legendreSym.at_neg_one hp2,
      χ₄_eq_neg_one_pow hodd,sign_natCast]
  rw [hs]
  generalize ((p/2 : ℕ) : ZMod 2)=s
  fin_cases s <;> norm_num [sign]

/-- The full support parity is obtained from the actual product11mod12,
not assumed independently of the twist parameter. -/
theorem actual_total_parity {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp2 : ∀ i, p i ≠ 2)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) :
    (∑ i, ((p i/2 : ℕ) : ZMod 2))=1 := by
  have hodd (i : ι) : p i % 2=1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : (p i).Prime)).mpr (hp2 i)
  have hfour : ((∏ i, p i : ℕ) : ZMod 4)=3 := by
    have h := congrArg (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) hn
    norm_num only [map_natCast,map_ofNat] at h
    exact h
  apply sign_injective
  rw [sign_sum,sign_one]
  calc
    (∏ i, sign ((p i/2 : ℕ) : ZMod 2)) = ∏ i, χ₄ (p i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [sign_natCast,χ₄_eq_neg_one_pow (hodd i)]
    _ = χ₄ ((∏ i, p i : ℕ) : ZMod 4) := by rw [Nat.cast_prod,map_prod]
    _ = -1 := by rw [hfour]; rfl

end ActualTwoDescentSupportParity318
