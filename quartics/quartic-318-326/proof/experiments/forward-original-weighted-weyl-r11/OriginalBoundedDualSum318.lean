module
public import NonzeroMultipleBox318
public section
noncomputable section
namespace OriginalBoundedDualSum318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalDualIncidenceCount318 NonzeroMultipleBox318
open TriangularLatticeBoxCount318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def subsetModulus (p : ι → ℕ) (s : Finset ι) : ℕ := ∏ i∈s, p i
@[expose] def zeroSubset (p : ι → ℕ) (v : Vector ℤ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => TernaryCongruenceLattices318.reduce (p i) v=0)

lemma zeroModulus_eq (p : ι → ℕ) (v : Vector ℤ) :
    zeroModulus p v=subsetModulus p (zeroSubset p v) := by
  classical
  simp only [subsetModulus,zeroSubset,Finset.prod_filter,zeroModulus]

lemma subset_modulus_pos (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (s : Finset ι) :
    0<subsetModulus p s := by
  exact Finset.prod_pos (fun i hi => (hp i).pos)

/-- Product divisibility is supplied by the actual CRT of the selected
DISTINCT primes; it is not inferred from coordinatewise congruences with
possibly repeated moduli. -/
lemma subset_divisor_iff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (s : Finset ι) (n : ℤ) :
    (subsetModulus p s:ℤ)∣n ↔ ∀ i∈s, (p i:ℤ)∣n := by
  classical
  have he : FixedSquarefreeCRT318.modulus (fun i : s => p i)=subsetModulus p s := by
    unfold FixedSquarefreeCRT318.modulus subsetModulus
    rw [Finset.prod_coe_sort_eq_attach,Finset.prod_attach]
  rw [←he,SquarefreeTernaryLatticeCover318.product_divisor_iff
    (fun i : s => p i) (fun i => hp i) (hd.comp Subtype.val_injective)]
  exact ⟨fun h i hi => h ⟨i,hi⟩, fun h i => h i i.2⟩

lemma zeroSubset_divides (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (v : Vector ℤ) :
    Divides (subsetModulus p (zeroSubset p v)) v := by
  classical
  have hh (i : ι) (hi : i∈zeroSubset p v) :
      (p i:ℤ)∣v.1 ∧ (p i:ℤ)∣v.2.1 ∧ (p i:ℤ)∣v.2.2 :=
    (zero_reduction_iff (p i) v).mp (Finset.mem_filter.mp hi).2
  exact ⟨(subset_divisor_iff p hp hd _ _).mpr (fun i hi => (hh i hi).1),
    (subset_divisor_iff p hp hd _ _).mpr (fun i hi => (hh i hi).2.1),
    (subset_divisor_iff p hp hd _ _).mpr (fun i hi => (hh i hi).2.2)⟩

/-- Keep every genuine coordinate-divisibility exception. An upper bound
by all prime subsets is an explicit overcount, not an equality or a
primitive-vector assumption. -/
lemma zeroModulus_majorant (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (v : Vector ℤ) :
    zeroModulus p v≤∑ s∈(Finset.univ : Finset ι).powerset,
      if Divides (subsetModulus p s) v then subsetModulus p s else 0 := by
  classical
  have hs : zeroSubset p v∈(Finset.univ : Finset ι).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hh := Finset.single_le_sum (f := fun s : Finset ι =>
      if Divides (subsetModulus p s) v then subsetModulus p s else 0)
    (fun s hs => Nat.zero_le _) hs
  simpa only [if_pos (zeroSubset_divides p hp hd v),←zeroModulus_eq p v] using hh

lemma weighted_indicator_sum (B d : ℕ) :
    (∑ v : NonzeroBox B, if Divides d (coordinates v.1) then d else 0)=
      d*Nat.card (MultipleBox B d) := by
  classical
  have hc : (∑ v : NonzeroBox B, if Divides d (coordinates v.1) then 1 else 0)=
      Nat.card (MultipleBox B d) := by
    simp only [MultipleBox,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter]
  rw [←hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> simp only [mul_one,mul_zero]

/-- Sum of the ACTUAL coordinate-gcd exception over bounded NONZERO
original vectors. The proof includes d>B, the empty prime set, and B=0. -/
theorem zeroModulus_sum_bound (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (B : ℕ) :
    (∑ v : NonzeroBox B, zeroModulus p (coordinates v.1))≤
      2^(Fintype.card ι)*(27*B^3) := by
  classical
  calc
    _ ≤ ∑ v : NonzeroBox B, ∑ s∈(Finset.univ : Finset ι).powerset,
        if Divides (subsetModulus p s) (coordinates v.1) then subsetModulus p s else 0 := by
      exact Finset.sum_le_sum (fun v hv => zeroModulus_majorant p hp hd _)
    _ = ∑ s∈(Finset.univ : Finset ι).powerset,
        ∑ v : NonzeroBox B,
          if Divides (subsetModulus p s) (coordinates v.1) then subsetModulus p s else 0 :=
      Finset.sum_comm
    _ = ∑ s∈(Finset.univ : Finset ι).powerset,
        subsetModulus p s*Nat.card (MultipleBox B (subsetModulus p s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact weighted_indicator_sum B _
    _ ≤ ∑ _s∈(Finset.univ : Finset ι).powerset, 27*B^3 := by
      exact Finset.sum_le_sum (fun s hs => weighted_count B _ (subset_modulus_pos p hp s))
    _ = 2^(Fintype.card ι)*(27*B^3) := by
      simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,nsmul_eq_mul]

/-- Concrete bounded-vector incidence sum for the original integer
lattice family. No real-lattice transference or successive-minimum
implication is smuggled into this statement. -/
theorem original_bounded_dual_sum (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (B : ℕ) :
    (∑ v : NonzeroBox B, Nat.card (Incidence p κ (coordinates v.1)))≤
      27*4^(Fintype.card ι)*B^3 := by
  classical
  calc
    _ ≤ ∑ v : NonzeroBox B, 2^(Fintype.card ι)*zeroModulus p (coordinates v.1) :=
      Finset.sum_le_sum (fun v hv => original_incidence_bound p hp hd κ hκ _)
    _ = 2^(Fintype.card ι)*(∑ v : NonzeroBox B, zeroModulus p (coordinates v.1)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2^(Fintype.card ι)*(2^(Fintype.card ι)*(27*B^3)) :=
      Nat.mul_le_mul_left _ (zeroModulus_sum_bound p hp hd B)
    _ = 27*4^(Fintype.card ι)*B^3 := by
      calc
        _ = 27*((2*2)^(Fintype.card ι))*B^3 := by rw [mul_pow]; ring
        _ = 27*4^(Fintype.card ι)*B^3 := by norm_num

end OriginalBoundedDualSum318
