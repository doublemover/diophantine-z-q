module
public import ActualTZPrimeSupportCRT318
public import ActualTZOneLinearDivisorCRT318
public section
noncomputable section
namespace ActualTZMultiLinearCRT318
open scoped BigOperators
open ActualTZResidueIntervalCount318

variable {I : Type*} [Fintype I]

def support (d : I→ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ : Finset I).biUnion fun i => (d i).primeFactors

theorem mem_support (d : I→ℕ) (p : ℕ) : p∈support d ↔ ∃ i,p∈(d i).primeFactors := by
  classical
  simp only [support,Finset.mem_biUnion,Finset.mem_univ,true_and]

theorem prime_mem (d : I→ℕ) (p : ℕ) (h : p∈support d) : p.Prime := by
  obtain ⟨i,hi⟩ := (mem_support d p).mp h
  exact (Nat.mem_primeFactors.mp hi).1

def modulus (d : I→ℕ) : ℕ := ActualTZPrimeSupportCRT318.modulus (support d)

theorem modulus_pos (d : I→ℕ) : 0 < modulus d :=
  ActualTZPrimeSupportCRT318.modulus_pos (support d) (prime_mem d)

theorem modulus_dvd_iff (d : I→ℕ) (hs : ∀ i,Squarefree (d i)) (z : ℤ) :
    (modulus d:ℤ)∣z ↔ ∀ i,(d i:ℤ)∣z := by
  have h (i : I) : (ActualTZPrimeSupportCRT318.modulus (d i).primeFactors:ℤ)=(d i:ℤ) := by
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree (hs i))
  rw [modulus,ActualTZPrimeSupportCRT318.prod_dvd_iff _ (prime_mem d)]
  constructor
  · intro H i
    rw [←h i,ActualTZPrimeSupportCRT318.prod_dvd_iff _
      (fun p hp => (Nat.mem_primeFactors.mp hp).1)]
    exact fun p hp => H p ((mem_support d p).mpr ⟨i,hp⟩)
  · intro H p hp
    obtain ⟨i,hi⟩ := (mem_support d p).mp hp
    have T := H i
    rw [←h i,ActualTZPrimeSupportCRT318.prod_dvd_iff _
      (fun q hq => (Nat.mem_primeFactors.mp hq).1)] at T
    exact T p hi

theorem nat_modulus_least (d : I→ℕ) (hs : ∀ i,Squarefree (d i)) (q : ℕ) :
    modulus d∣q ↔ ∀i,d i∣q := by
  rw [←Int.natCast_dvd_natCast,modulus_dvd_iff d hs]
  simp only [Int.natCast_dvd_natCast]

def physicalConst (W : ℕ) (a : I→ℤ) (b : I→ℕ) (i : I) : ℤ :=
  (W:ℤ)*a i+b i

def Compatible (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ) : Prop :=
  (∀ i,W.Coprime (d i)) ∧
  ∀ i j p, p.Prime→p∣d i→p∣d j→(p:ℤ)∣physicalConst W a b i-physicalConst W a b j

def Fits (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ) (x : ℤ) : Prop :=
  ∀ i,(d i:ℤ)∣(W:ℤ)*x+physicalConst W a b i

private def root (W p : ℕ) (c : ℤ) : ℤ := -Nat.gcdA W p*c

private theorem has_root (W p : ℕ) (c : ℤ) (hc : W.Coprime p) :
    (p:ℤ)∣(W:ℤ)*root W p c+c := by
  exact (ActualTZOneLinearDivisorCRT318.bezout_class W p c _ hc).mpr (Int.ModEq.refl _)

/-- Literal residue comparison on a shared prime. No polynomial is
specialized out of the pair difference: c and c' can be the two
original physical constants with their signed shifts / wrap offsets. -/
theorem assigned_roots_agree (W p : ℕ) (c c' : ℤ) (hc : W.Coprime p) :
    Int.ModEq (p:ℤ) (-Nat.gcdA W p*c) (-Nat.gcdA W p*c') ↔ (p:ℤ)∣c-c' := by
  have h₀ := has_root W p c' hc
  have h₁ : Int.ModEq (p:ℤ) (root W p c) (root W p c') ↔
      (p:ℤ)∣(W:ℤ)*root W p c'+c :=
    (ActualTZOneLinearDivisorCRT318.bezout_class W p c _ hc).symm
  change Int.ModEq (p:ℤ) (root W p c) (root W p c') ↔ (p:ℤ)∣c-c'
  rw [h₁]
  constructor
  · intro hd
    have h := dvd_sub hd h₀
    rwa [show (W:ℤ)*root W p c'+c-((W:ℤ)*root W p c'+c')=c-c' by ring] at h
  · intro hd
    have h := dvd_add h₀ hd
    rwa [show (W:ℤ)*root W p c'+c'+(c-c')=(W:ℤ)*root W p c'+c by ring] at h

theorem compatible_of_fits (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (hUnit : ∀ i,W.Coprime (b i)) (x : ℤ) (hx : Fits W d a b x) :
    Compatible W d a b := by
  constructor
  · intro i
    by_contra H
    apply ActualTZOneLinearDivisorCRT318.noncoprime_no_hit W (d i) (b i) (hUnit i) H x (a i)
    simpa only [physicalConst,mul_add,add_assoc] using hx i
  · intro i j p _ hd he
    have h₁ := (Int.natCast_dvd_natCast.mpr hd).trans (hx i)
    have h₂ := (Int.natCast_dvd_natCast.mpr he).trans (hx j)
    have h := dvd_sub h₁ h₂
    rwa [show (W:ℤ)*x+physicalConst W a b i-((W:ℤ)*x+physicalConst W a b j)=
      physicalConst W a b i-physicalConst W a b j by ring] at h

theorem lift_fits (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (hs : ∀ i,Squarefree (d i)) (hC : Compatible W d a b) :
    ∃ r : ℤ,Fits W d a b r := by
  classical
  let chosen (p : ℕ) (hp : p∈support d) := Classical.choose ((mem_support d p).mp hp)
  have chosen_mem (p : ℕ) (hp : p∈support d) :
      p∈(d (chosen p hp)).primeFactors := Classical.choose_spec ((mem_support d p).mp hp)
  let roots (p : ℕ) : ℤ :=
    if hp : p∈support d then root W p (physicalConst W a b (chosen p hp)) else 0
  obtain ⟨r,hr⟩ := ActualTZPrimeSupportCRT318.lift (support d) (prime_mem d) roots
  refine ⟨r,?_⟩
  intro i
  have hEQ : ActualTZPrimeSupportCRT318.modulus (d i).primeFactors=d i :=
    Nat.prod_primeFactors_of_squarefree (hs i)
  rw [←hEQ,ActualTZPrimeSupportCRT318.prod_dvd_iff _
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)]
  intro p hp
  have hS := (mem_support d p).mpr ⟨i,hp⟩
  have hPi := (Nat.mem_primeFactors.mp hp).2.1
  have hj := (Nat.mem_primeFactors.mp (chosen_mem p hS)).2.1
  have hc : W.Coprime p := (hC.1 i).of_dvd_right hPi
  have hR := hr p hS
  simp only [roots,dif_pos hS] at hR
  have hAgree : Int.ModEq (p:ℤ) (root W p (physicalConst W a b i))
      (root W p (physicalConst W a b (chosen p hS))) :=
    (assigned_roots_agree W p _ _ hc).mpr (hC.2 i (chosen p hS) p (prime_mem d p hS) hPi hj)
  exact (ActualTZOneLinearDivisorCRT318.bezout_class W p _ _ hc).mpr (hAgree.trans hR.symm)

theorem fits_iff_class (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (hs : ∀ i,Squarefree (d i)) (hC : Compatible W d a b) (r : ℤ) (hr : Fits W d a b r)
    (x : ℤ) : Fits W d a b x ↔ Int.ModEq (modulus d:ℤ) x r := by
  have h (i : I) : (d i:ℤ)∣(W:ℤ)*x+physicalConst W a b i ↔ Int.ModEq (d i:ℤ) x r := by
    have hroot := (ActualTZOneLinearDivisorCRT318.bezout_class W (d i) _ _ (hC.1 i)).mp (hr i)
    rw [ActualTZOneLinearDivisorCRT318.bezout_class W (d i) _ _ (hC.1 i)]
    constructor
    · intro hx
      exact hx.symm.trans hroot
    · intro hx
      exact hroot.trans hx.symm
  simp only [Fits,h,Int.modEq_iff_dvd,modulus_dvd_iff d hs]

theorem exact_support (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (hs : ∀ i,Squarefree (d i)) (hUnit : ∀ i,W.Coprime (b i)) :
    (∃ x : ℤ,Fits W d a b x) ↔ Compatible W d a b :=
  ⟨fun ⟨x,hx⟩ => compatible_of_fits W d a b hUnit x hx, lift_fits W d a b hs⟩

def jointCount (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ) (L : ℕ) (s : ℤ) : ℕ := by
  classical
  exact ∑ t∈Finset.range L,if Fits W d a b (s+(t:ℤ)) then 1 else 0

def jointDensity (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ) : ℝ := by
  classical
  exact if Compatible W d a b then 1/(modulus d:ℝ) else 0

theorem count_of_compatible (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (L : ℕ) (s : ℤ) (hs : ∀ i,Squarefree (d i)) (hC : Compatible W d a b) :
    ∃ r : ℤ,Fits W d a b r ∧ jointCount W d a b L s =
      L/modulus d+(if ((r-s)%(modulus d:ℤ)).toNat<L%modulus d then 1 else 0) := by
  classical
  obtain ⟨r,hr⟩ := lift_fits W d a b hs hC
  have hEq : jointCount W d a b L s=intHits (modulus d) L s r := by
    unfold jointCount intHits
    apply Finset.sum_congr rfl
    intro t _
    have he := fits_iff_class W d a b hs hC r hr (s+(t:ℤ))
    by_cases ht : Fits W d a b (s+(t:ℤ))
    · simp only [if_pos ht,if_pos (he.mp ht)]
    · simp only [if_neg ht,if_neg (fun hk=>ht (he.mpr hk))]
  exact ⟨r,hr,hEq.trans (exact_int_count _ _ _ _ (modulus_pos d))⟩

theorem normalized_round (W : ℕ) (d : I→ℕ) (a : I→ℤ) (b : I→ℕ)
    (L : ℕ) (s : ℤ) (hs : ∀ i,Squarefree (d i))
    (hUnit : ∀ i,W.Coprime (b i)) (hL : 0<L) :
    |(jointCount W d a b L s:ℝ)/(L:ℝ)-jointDensity W d a b| ≤ 1/(L:ℝ) := by
  classical
  have hLR : (0:ℝ)<L := by exact_mod_cast hL
  by_cases H : Compatible W d a b
  · obtain ⟨r,hr⟩ := lift_fits W d a b hs H
    have hEq : jointCount W d a b L s=intHits (modulus d) L s r := by
      unfold jointCount intHits
      apply Finset.sum_congr rfl
      intro t _
      have he := fits_iff_class W d a b hs H r hr (s+(t:ℤ))
      by_cases ht : Fits W d a b (s+(t:ℤ))
      · simp only [if_pos ht,if_pos (he.mp ht)]
      · simp only [if_neg ht,if_neg (fun hk=>ht (he.mpr hk))]
    rw [hEq,jointDensity,if_pos H]
    have hqR : (0:ℝ) < (modulus d:ℝ) := by exact_mod_cast modulus_pos d
    have hh : (intHits (modulus d) L s r:ℝ)/(L:ℝ)-1/(modulus d:ℝ) =
        ((intHits (modulus d) L s r:ℝ)-(L:ℝ)/(modulus d:ℝ))/(L:ℝ) := by
      field_simp [hLR.ne',hqR.ne'] <;> ring
    rw [hh,abs_div,abs_of_nonneg hLR.le]
    exact div_le_div_of_nonneg_right (int_count_error _ _ _ _ (modulus_pos d)) hLR.le
  · have hNo (x : ℤ) : ¬Fits W d a b x := fun hx => H (compatible_of_fits W d a b hUnit x hx)
    simp only [jointCount,hNo,if_false,Finset.sum_const_zero,Nat.cast_zero,
      zero_div,jointDensity,if_neg H,sub_zero,abs_zero]
    positivity

end ActualTZMultiLinearCRT318
