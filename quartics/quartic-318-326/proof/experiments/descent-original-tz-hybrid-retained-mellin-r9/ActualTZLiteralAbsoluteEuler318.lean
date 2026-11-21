module
public import ActualTZPositiveEulerMajorant318
public import ActualTZRegulatedPhysicalBounds318
import all ActualTZRegulatedPhysicalBounds318
public section
noncomputable section
namespace ActualTZLiteralAbsoluteEuler318
open scoped BigOperators
open ActualTZPositiveEulerMajorant318
open ActualTZRegulatedPhysicalBounds318 ActualTZRegulatedPhysicalPrime318 ActualTZRegulatedLocalFactor318
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Pair (I : Type*) := Bits I × Bits I

@[expose] def offCount (I : Type*) [Fintype I] : ℕ := 4^Fintype.card I-1

@[expose] def allOff : Pair I := (emptyBits,emptyBits)

theorem pair_card : Fintype.card (Pair I)=4^Fintype.card I := by
  simp only [Pair,Bits,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,←mul_pow] <;> norm_num

theorem nonempty_card :
    ((Finset.univ : Finset (Pair I)).erase allOff).card=offCount I := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,pair_card,offCount]

private theorem no_selected_iff (d : Pair I) :
    (∀ i,¬selected d.1 d.2 i) ↔ d=allOff := by
  cases d with
  | mk f g =>
    constructor
    · intro h
      apply Prod.ext
      · funext i
        cases H : f i
        · exact H
        · exact (h i (Or.inl H)).elim
      · funext i
        cases H : g i
        · exact H
        · exact (h i (Or.inr H)).elim
    · rintro h
      have H₁ := congrArg Prod.fst h
      have H₂ := congrArg Prod.snd h
      change f=emptyBits at H₁
      change g=emptyBits at H₂
      simp [H₁,H₂,emptyBits,selected]

@[expose] def term (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (s u : I→ℂ) (d : Pair I) : ℂ :=
  amplitude (regulator p s) (regulator p u) d.1 d.2*physicalMass W p a b d.1 d.2

theorem all_off_term (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (s u : I→ℂ) :
    term W p a b s u allOff = 1 := by
  have H : ∀ i : I,¬selected emptyBits emptyBits i := by
    simp [emptyBits,selected]
  have hM : (physicalMass W p a b emptyBits emptyBits : ℂ)=1 := by
    by_cases hc : W.Coprime p
    · rw [physicalMass_incident W p a b _ _ hc,if_pos H]
    · rw [physicalMass_bad W p a b _ _ hU hc,if_pos H]
  simp [term,allOff,amplitude,pick,emptyBits,hM]

theorem nonempty_term (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ)
    (s u : I→ℂ) (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re)
    (d : Pair I) (hd : d≠allOff) :
    ‖term W p a b s u d‖≤q σ p := by
  have hno : ¬∀ i,¬selected d.1 d.2 i := fun H => hd ((no_selected_iff d).1 H)
  let t : ℝ := (p:ℝ)^(-σ)
  have h₀ : 0≤t := by dsimp only [t]; positivity
  have h₁ : t≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hp.one_lt.le) (by linarith)
  have norm_reg (v : I→ℂ) (hv : ∀ i,σ≤(v i).re) (i : I) :
      ‖regulator p v i‖≤t := by
    rw [regulator,Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (neg_le_neg (hv i))
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have he : t/(p:ℝ)=q σ p := by
    dsimp only [t,q]
    rw [show -1-σ=(-σ)-(1:ℝ) by ring,Real.rpow_sub hp',Real.rpow_one]
  rw [←he]
  have H := residual_norm W p a b hU (regulator p s) (regulator p u)
    t h₀ h₁ (norm_reg s hs) (norm_reg u hu) d.1 d.2
  simpa only [residual,if_neg hno,term] using H

@[expose] def absoluteAt (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ) : ℝ :=
  ∑ d : Pair I,‖term W p a b s u d‖

/-- Exactly one all-off pair contributes 1. The cardinal of the
remaining bit pairs is 4^k−1, including the possibility that both
slots of the same original row turn on. -/
theorem exact_local_budget (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    absoluteAt W p a b s u≤1+(offCount I:ℝ)*q σ p := by
  have hOff := all_off_term W p a b hU s u
  unfold absoluteAt
  rw [←Finset.sum_erase_add _ (Finset.mem_univ (allOff : Pair I)),hOff,norm_one]
  have hSum :
      (∑ d∈(Finset.univ : Finset (Pair I)).erase allOff,‖term W p a b s u d‖)≤
        (offCount I:ℝ)*q σ p := by
    calc
      _ ≤ ∑ _d∈(Finset.univ : Finset (Pair I)).erase allOff,q σ p := by
        apply Finset.sum_le_sum
        intro d hd
        exact nonempty_term W p hp a b hU σ hσ s u hs hu d ((Finset.mem_erase.mp hd).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,nonempty_card]
  linarith

def atNat (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ) : ℝ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    absoluteAt W p a b s u
  else 1

theorem actual_product_budget (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    (∏ p∈Nat.primesBelow P,atNat W p a b s u) ≤ ‖riemannZeta ((1+σ:ℝ):ℂ)‖^(offCount I) := by
  apply zeta_power σ hσ P (offCount I)
  · intro p hp
    rw [atNat,dif_pos (Nat.prime_of_mem_primesBelow hp)]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · intro p hp
    have h := Nat.prime_of_mem_primesBelow hp
    letI : NeZero p := ⟨h.ne_zero⟩
    rw [atNat,dif_pos h]
    exact exact_local_budget W p h a b hU σ hσ s u hs hu

abbrev PrimeAt (P : ℕ) := ↥(Nat.primesBelow P)
abbrev Choices (I : Type*) (P : ℕ) := PrimeAt P → Pair I

def entry (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ)
    (p : PrimeAt P) (d : Pair I) : ℂ :=
  let hp := Nat.prime_of_mem_primesBelow p.property
  letI : NeZero p.val := ⟨hp.ne_zero⟩
  term W p.val a b s u d

def choiceWeight (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ)
    (d : Choices I P) : ℂ :=
  ∏ p : PrimeAt P,entry W P a b s u p (d p)

/-- The ABSOLUTE assignment table factors exactly over any finite
prime universe; this is not the norm of a signed sum, and imposes
no divisor size cutoff at its intermediate step. -/
theorem choice_absolute_eq (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ) :
    (∑ d : Choices I P,‖choiceWeight W P a b s u d‖) =
      ∏ p∈Nat.primesBelow P,atNat W p a b s u := by
  classical
  calc
    _ = ∑ d : Choices I P,∏ p : PrimeAt P,‖entry W P a b s u p (d p)‖ := by
      simp only [choiceWeight,Complex.norm_prod]
    _ = ∏ p : PrimeAt P,∑ d : Pair I,‖entry W P a b s u p d‖ := by
      rw [Fintype.prod_sum]
    _ = ∏ p : PrimeAt P,atNat W p.val a b s u := by
      apply Finset.prod_congr rfl
      intro p _
      have hp := Nat.prime_of_mem_primesBelow p.property
      rw [atNat,dif_pos hp,absoluteAt]
      rfl
    _ = _ := Finset.prod_coe_sort _ _

theorem assignment_zeta (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    (∑ d : Choices I P,‖choiceWeight W P a b s u d‖) ≤
        ‖riemannZeta ((1+σ:ℝ):ℂ)‖^(offCount I) := by
  rw [choice_absolute_eq]
  exact actual_product_budget W P a b hU σ hσ s u hs hu

end ActualTZLiteralAbsoluteEuler318
