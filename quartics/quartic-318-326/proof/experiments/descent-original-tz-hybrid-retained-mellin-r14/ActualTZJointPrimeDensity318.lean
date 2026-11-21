module
public import ActualTZRegulatedPhysicalPrime318
import all ActualTZMultiLinearCRT318
public section
noncomputable section
namespace ActualTZJointPrimeDensity318
open scoped BigOperators
open ActualTZMultiLinearCRT318 ActualTZRegulatedLocalFactor318 ActualTZRegulatedPhysicalPrime318
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev Slot (I : Type*) := I × Bool
abbrev DigitTable (I : Type*) := Slot I → ℕ

@[expose] def pickPrime (d : DigitTable I) (p : ℕ) (s : Bool) : Bits I :=
  fun i => decide (p∣d (i,s))

theorem pickPrime_true (d : DigitTable I) (p : ℕ) (s : Bool) (i : I) :
    pickPrime d p s i=true ↔ p∣d (i,s) := by
  simp only [pickPrime,decide_eq_true_eq]

theorem selected_prime (d : DigitTable I) (p : ℕ) (i : I) :
    selected (pickPrime d p true) (pickPrime d p false) i ↔ ∃ s : Bool,p∣d (i,s) := by
  simp only [selected,pickPrime_true]
  constructor
  · rintro (h|h)
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  · rintro ⟨s,h⟩
    cases s
    · exact Or.inr h
    · exact Or.inl h

private theorem support_of_dvd (d : DigitTable I) (hD : ∀ j,Squarefree (d j))
    (p : ℕ) (hp : p.Prime) (j : Slot I) (h : p∣d j) : p∈support d :=
  (mem_support d p).2 ⟨j,Nat.mem_primeFactors.2 ⟨hp,h,(hD j).ne_zero⟩⟩

private theorem used_of_mem (d : DigitTable I) (p : ℕ) (h : p∈support d) :
    ∃ i,selected (pickPrime d p true) (pickPrime d p false) i := by
  obtain ⟨⟨i,b⟩,hp⟩ := (mem_support d p).1 h
  exact ⟨i,(selected_prime d p i).2 ⟨b,(Nat.mem_primeFactors.1 hp).2.1⟩⟩

@[expose] def Local (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I) : Prop :=
  W.Coprime p ∧ ∀ i j,
    selected (pickPrime d p true) (pickPrime d p false) i →
    selected (pickPrime d p true) (pickPrime d p false) j →
    (p:ℤ)∣physicalConst W a b i-physicalConst W a b j

private theorem slot_const (W : ℕ) (a : I→ℤ) (b : I→ℕ) (j : Slot I) :
    physicalConst W (a ∘ Prod.fst) (b ∘ Prod.fst) j=physicalConst W a b j.1 := by
  unfold physicalConst
  rfl

/-- The same two original divisor slots, not independent sites, give
one real congruence in x at each used prime; no repeated prime in Q. -/
theorem global_iff_local (W : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I)
    (hD : ∀ j,Squarefree (d j)) :
    Compatible W d (a ∘ Prod.fst) (b ∘ Prod.fst) ↔
      ∀ p∈support d,Local W p a b d := by
  constructor
  · intro H p hp
    obtain ⟨j,hj⟩ := (mem_support d p).1 hp
    have hC := (H.1 j).of_dvd_right ((Nat.mem_primeFactors.1 hj).2.1)
    refine ⟨hC,?_⟩
    intro i k hi hk
    obtain ⟨c,hc⟩ := (selected_prime d p i).1 hi
    obtain ⟨c',hc'⟩ := (selected_prime d p k).1 hk
    simpa only [slot_const] using H.2 (i,c) (k,c') p (prime_mem d p hp) hc hc'
  · intro H
    constructor
    · intro j
      by_contra h
      obtain ⟨p,hp,hW,hd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      have hLocal := H p (support_of_dvd d hD p hp j hd)
      exact (hp.dvd_iff_not_coprime.mp hW) hLocal.1.symm
    · intro i j p hp hi hj
      have h := H p (support_of_dvd d hD p hp i hi)
      have hi' := (selected_prime d p i.1).2 ⟨i.2,hi⟩
      have hj' := (selected_prime d p j.1).2 ⟨j.2,hj⟩
      simpa only [slot_const] using h.2 i.1 j.1 hi' hj'

theorem fits_iff_local (W : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I)
    (hD : ∀ j,Squarefree (d j)) (hU : ∀ i,W.Coprime (b i)) :
    (∃ x : ℤ,Fits W d (a ∘ Prod.fst) (b ∘ Prod.fst) x) ↔
      ∀ p∈support d,Local W p a b d :=
  (exact_support W d (a ∘ Prod.fst) (b ∘ Prod.fst) hD (fun j => hU j.1)).trans
    (global_iff_local W a b d hD)

def massAt (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I) : ℂ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    physicalMass W p a b (pickPrime d p true) (pickPrime d p false)
  else 1

theorem used_mass (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I)
    (hU : ∀ i,W.Coprime (b i)) (hp : p∈support d) :
    massAt W p a b d = if Local W p a b d then 1/(p:ℂ) else 0 := by
  have hp' := prime_mem d p hp
  letI : NeZero p := ⟨hp'.ne_zero⟩
  obtain ⟨i,hi⟩ := used_of_mem d p hp
  have he : ¬∀ i,¬selected (pickPrime d p true) (pickPrime d p false) i :=
    fun H => H i hi
  rw [massAt,dif_pos hp']
  by_cases hc : W.Coprime p
  · rw [physicalMass_incident W p a b _ _ hc,if_neg he]
    simp only [Local,hc,true_and]
  · rw [physicalMass_bad W p a b _ _ hU hc,if_neg he]
    simp only [Local,hc,false_and,if_false]

theorem unused_mass (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (d : DigitTable I)
    (hD : ∀ j,Squarefree (d j)) (hU : ∀ i,W.Coprime (b i)) (hp : p∉support d) :
    massAt W p a b d=1 := by
  unfold massAt
  by_cases hp' : p.Prime
  · rw [dif_pos hp']
    have he : ∀ i,¬selected (pickPrime d p true) (pickPrime d p false) i := by
      intro i hi
      obtain ⟨c,hc⟩ := (selected_prime d p i).1 hi
      exact hp (support_of_dvd d hD p hp' (i,c) hc)
    letI : NeZero p := ⟨hp'.ne_zero⟩
    by_cases hc : W.Coprime p
    · rw [physicalMass_incident W p a b _ _ hc,if_pos he]
    · rw [physicalMass_bad W p a b _ _ hU hc,if_pos he]
  · rw [dif_neg hp']

theorem density_eq_support_product (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (d : DigitTable I) (hD : ∀ j,Squarefree (d j)) (hU : ∀ i,W.Coprime (b i)) :
    (jointDensity W d (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)=∏ p∈support d,massAt W p a b d := by
  classical
  unfold jointDensity
  by_cases hc : Compatible W d (a ∘ Prod.fst) (b ∘ Prod.fst)
  · rw [if_pos hc,Complex.ofReal_div,Complex.ofReal_one]
    have H := (global_iff_local W a b d hD).1 hc
    calc
      _ = ∏ p∈support d,1/(p:ℂ) := by
        simp only [modulus,ActualTZPrimeSupportCRT318.modulus,Complex.ofReal_natCast,
          Nat.cast_prod,one_div,Finset.prod_inv_distrib]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [used_mass W p a b d hU hp,if_pos (H p hp)]
  · rw [if_neg hc,Complex.ofReal_zero]
    have hh : ∃ p∈support d,¬Local W p a b d := by
      by_contra hn
      apply hc
      apply (global_iff_local W a b d hD).2
      intro p hp
      by_contra hl
      exact hn ⟨p,hp,hl⟩
    obtain ⟨p,hp,hl⟩ := hh
    symm
    apply Finset.prod_eq_zero hp
    rw [used_mass W p a b d hU hp,if_neg hl]

theorem density_eq_universe_product (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (d : DigitTable I) (hD : ∀ j,Squarefree (d j)) (hU : ∀ i,W.Coprime (b i))
    (P : ℕ) (hP : ∀ j,(d j).primeFactors⊆Nat.primesBelow P) :
    (jointDensity W d (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)=
      ∏ p∈Nat.primesBelow P,massAt W p a b d := by
  rw [density_eq_support_product W a b d hD hU]
  have h : support d⊆Nat.primesBelow P := by
    intro p hp
    obtain ⟨j,hj⟩ := (mem_support d p).1 hp
    exact hP j hj
  exact Finset.prod_subset h (fun p _ hnot => unused_mass W p a b d hD hU hnot)

end ActualTZJointPrimeDensity318
