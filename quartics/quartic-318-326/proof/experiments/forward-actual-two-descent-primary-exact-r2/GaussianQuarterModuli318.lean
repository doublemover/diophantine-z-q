module
public import GaussianNeighborNorms318
public section
noncomputable section
namespace GaussianQuarterModuli318
open GaussianNeighborNorms318
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- The exact finite avoidance conclusion still required from the chosen
Gaussian rays. It only concerns odd prime divisors of the prior L. -/
@[expose] def Avoid (L : ℕ) (a b : ℤ) : Prop := ∀ p : ℕ, p.Prime → p∣L → p≠2 →
  ¬p∣minus a b ∧ ¬p∣plus a b

lemma odd_coprime_of_avoid (L n N : ℕ) (hn : Odd n) (hnN : n∣N)
    (havoid : ∀ p : ℕ, p.Prime → p∣L → p≠2 → ¬p∣N) : Nat.Coprime n L := by
  apply Nat.coprime_of_dvd'
  intro p hp hpn hpL
  by_cases he : p=2
  · subst p
    obtain ⟨k,hk⟩ := hpn
    obtain ⟨l,hl⟩ := hn
    omega
  · exact False.elim (havoid p hp hpL he (hpn.trans hnN))

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (a b : ι → ℤ)
@[expose] def lower : ℕ := Finset.univ.lcm (fun i => minus (a i) (b i)/4)
@[expose] def upper : ℕ := Finset.univ.lcm (fun i => plus (a i) (b i)/4)

lemma lcm_coprime {κ : Type*} [Fintype κ] (f : ι → ℕ) (g : κ → ℕ)
    (hc : ∀ i j, Nat.Coprime (f i) (g j)) :
    Nat.Coprime (Finset.univ.lcm f) (Finset.univ.lcm g) := by
  have hh : Nat.Coprime (∏ i, f i) (∏ j, g j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact Nat.coprime_prod_right_iff.mpr (fun j hj => hc i j)
  exact (hh.of_dvd_left (Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem f hi))).of_dvd_right
    (Finset.lcm_dvd (fun j hj => Finset.dvd_prod_of_mem g hj))

theorem positive (ha : ∀ i, a i%16=9) (hb : ∀ i, b i%16=0) :
    0<lower a b ∧ 0<upper a b := by
  constructor
  · apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun i hi => (quarters (a i) (b i) (ha i) (hb i)).1.ne')
  · apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun i hi => (quarters (a i) (b i) (ha i) (hb i)).2.1.ne')

/-- The all-position gcd-four condition is consumed literally, including
cross-position and repeated-index comparisons. -/
theorem pair_coprime (ha : ∀ i, a i%16=9) (hb : ∀ i, b i%16=0)
    (hpair : ∀ i j, Nat.gcd (minus (a i) (b i)) (plus (a j) (b j))=4) :
    Nat.Coprime (lower a b) (upper a b) :=
  lcm_coprime _ _ (fun i j => quarter_coprime _ _ _ _ (ha i) (hb i) (ha j) (hb j) (hpair i j))

/-- Derive the exact shared factor16 and opposite coprimality with L from
actual neighboring-norm odd-prime avoidance and the signed ray factors. -/
theorem continuity_gcd (L : ℕ) (hL : 64∣L)
    (ha : ∀ i, a i%16=9) (hb : ∀ i, b i%16=0) (hav : ∀ i, Avoid L (a i) (b i)) :
    Nat.gcd (lower a b) L=16 ∧ Nat.Coprime (upper a b) L := by
  choose m n hm hn he hf using fun i => ray_factors (a i) (b i) (ha i) (hb i)
  have hqm : ∀ i, minus (a i) (b i)/4=16*m i := by intro i; have hh := he i; omega
  have hqp : ∀ i, plus (a i) (b i)/4=n i := by intro i; have hh := hf i; omega
  have hmL : ∀ i, Nat.Coprime (m i) L := by
    intro i
    apply odd_coprime_of_avoid L (m i) (minus (a i) (b i)) (hm i)
    · rw [he i]; exact dvd_mul_left _ _
    · exact fun p hp hpL hp2 => (hav i p hp hpL hp2).1
  have hnL : ∀ i, Nat.Coprime (n i) L := by
    intro i
    apply odd_coprime_of_avoid L (n i) (plus (a i) (b i)) (hn i)
    · rw [hf i]; exact dvd_mul_left _ _
    · exact fun p hp hpL hp2 => (hav i p hp hpL hp2).2
  let O := ∏ i, m i
  have hOL : Nat.Coprime O L := Nat.coprime_prod_left_iff.mpr (fun i hi => hmL i)
  have hlo : lower a b∣O*16 := by
    apply Finset.lcm_dvd
    intro i hi
    rw [hqm i,Nat.mul_comm 16]
    obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem m hi
    refine ⟨k,?_⟩
    change O*16=m i*16*k
    dsimp [O]
    rw [hk]
    ring
  have h16low : 16∣lower a b := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact ((quarters (a i) (b i) (ha i) (hb i)).2.2.1).trans
      (Finset.dvd_lcm (Finset.mem_univ i))
  have h16L : 16∣L := (show 16∣64 by norm_num).trans hL
  have hupper : Nat.Coprime (upper a b) L := by
    have hh : Nat.Coprime (∏ i, n i) L := Nat.coprime_prod_left_iff.mpr (fun i hi => hnL i)
    apply hh.of_dvd_left
    apply Finset.lcm_dvd
    intro i hi
    rw [hqp i]
    exact Finset.dvd_prod_of_mem n hi
  refine ⟨Nat.dvd_antisymm ?_ (Nat.dvd_gcd h16low h16L),hupper⟩
  have hd : Nat.gcd (lower a b) L∣Nat.gcd (O*16) L :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans hlo) (Nat.gcd_dvd_right _ _)
  have hg16 : Nat.gcd 16 L=16 := Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd dvd_rfl h16L)
  rwa [Nat.Coprime.gcd_mul_left_cancel 16 hOL,hg16] at hd

end GaussianQuarterModuli318
