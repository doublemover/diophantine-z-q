module
public import Mathlib
public section
noncomputable section
namespace ActualGaussianRayConjugateLift318

open scoped BigOperators

abbrev Pair := ℤ×ℤ

inductive Quarter where
  | one | i | negOne | negI
  deriving DecidableEq

@[expose] def rotate (e : Quarter) (z : Pair) : Pair :=
  match e with
  | .one => z
  | .i => (-z.2,z.1)
  | .negOne => (-z.1,-z.2)
  | .negI => (z.2,-z.1)

@[expose] def switch (bar : Bool) (z : Pair) : Pair :=
  if bar then (z.1,-z.2) else z

@[expose] def norm (z : Pair) : ℤ := z.1^2+z.2^2

@[expose] def adjacent (eps : ℤ) (z : Pair) : ℤ := (z.1+eps)^2+z.2^2

@[expose] def PairCongr (M : ℕ) (z t : Pair) : Prop :=
  z.1≡t.1 [ZMOD (M:ℤ)] ∧ z.2≡t.2 [ZMOD (M:ℤ)]

theorem rotate_norm (e : Quarter) (z : Pair) : norm (rotate e z)=norm z := by
  cases e <;> simp only [rotate,norm,Prod.fst,Prod.snd] <;> ring

theorem switch_norm (e : Bool) (z : Pair) : norm (switch e z)=norm z := by
  cases e <;> simp [switch,norm]

/-- Conjugation keeps EACH directed adjacent norm. Quarter-turns need
not do so, and are applied only to match the chosen residue class. -/
theorem switch_adjacent (e : Bool) (z : Pair) (eps : ℤ) :
    adjacent eps (switch e z)=adjacent eps z := by
  cases e <;> simp [switch,adjacent]

theorem switch_involutive (bar : Bool) (z : Pair) : switch bar (switch bar z)=z := by
  cases bar <;> simp [switch]

theorem switch_congr {M : ℕ} {z t : Pair} (h : PairCongr M z t) (bar : Bool) :
    PairCongr M (switch bar z) (switch bar t) := by
  cases bar
  · exact h
  · exact ⟨h.1,h.2.neg⟩

theorem reduce {M m : ℕ} {z t : Pair} (h : PairCongr M z t) (hm : m∣M) :
    PairCongr m z t := by
  have hd : (m:ℤ)∣(M:ℤ) := by exact_mod_cast hm
  exact ⟨Int.ModEq.of_dvd hd h.1,Int.ModEq.of_dvd hd h.2⟩

theorem pair_trans {M : ℕ} {z t w : Pair} (h : PairCongr M z t)
    (h' : PairCongr M t w) : PairCongr M z w :=
  ⟨h.1.trans h'.1,h.2.trans h'.2⟩

theorem adj_congr {M : ℕ} {z t : Pair} (h : PairCongr M z t) (e : ℤ) :
    adjacent e z ≡ adjacent e t [ZMOD (M:ℤ)] :=
  ((h.1.add_right e).pow 2).add (h.2.pow 2)

@[expose] def Safe (l : ℕ) (z : Pair) : Prop :=
  (¬(l:ℤ)∣adjacent (-1) z) ∧ ¬(l:ℤ)∣adjacent 1 z

theorem safe_transport {l : ℕ} {z t : Pair} (h : PairCongr l z t) (ht : Safe l t) :
    Safe l z := by
  constructor
  · intro hbad
    apply ht.1
    rw [Int.dvd_iff_emod_eq_zero] at hbad ⊢
    exact (adj_congr h (-1)).symm.trans hbad
  · intro hbad
    apply ht.2
    rw [Int.dvd_iff_emod_eq_zero] at hbad ⊢
    exact (adj_congr h 1).symm.trans hbad

theorem safe_base_i {l : ℕ} {z : Pair} (hp : Nat.Prime l) (ho : l≠2)
    (h : PairCongr l z (0,1)) : Safe l z := by
  apply safe_transport h
  have htwo : ¬(l:ℤ)∣(2:ℤ) := by
    intro H
    have H' : l∣2 := by exact_mod_cast H
    exact ho ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp H')
  have h₋ : adjacent (-1) (0,1)=(2:ℤ) := by norm_num [adjacent]
  have h₊ : adjacent 1 (0,1)=(2:ℤ) := by norm_num [adjacent]
  exact ⟨fun h => htwo (h₋ ▸ h),fun h => htwo (h₊ ▸ h)⟩

theorem safe_base_7 {z : Pair} (h : PairCongr 7 z (1,3)) : Safe 7 z := by
  apply safe_transport h
  norm_num [Safe,adjacent,Int.dvd_iff_emod_eq_zero]

theorem combine_3_17 {x : ℤ} (a : (3:ℤ)∣x) (b : (17:ℤ)∣x) : (51:ℤ)∣x := by
  obtain ⟨u,hu⟩ := a
  obtain ⟨v,hv⟩ := b
  refine ⟨6*v-u,?_⟩
  linear_combination 18*hv-17*hu

theorem pair_51 {z t : Pair} (h3 : PairCongr 3 z t) (h17 : PairCongr 17 z t) :
    PairCongr 51 z t := by
  constructor
  · exact Int.modEq_iff_dvd.mpr (combine_3_17 h3.1.dvd h17.1.dvd)
  · exact Int.modEq_iff_dvd.mpr (combine_3_17 h3.2.dvd h17.2.dvd)

/-- No second unit preserves the real-9, imaginary-0 signed ray. -/
theorem unit_for_fixed_ray {e : Quarter} {z : Pair} (hz : PairCongr 16 z (9,0))
    (he : PairCongr 16 (rotate e z) (9,0)) : e=.one := by
  rcases z with ⟨a,b⟩
  have hA : a%16=9 := by simpa [PairCongr,Int.ModEq] using hz.1
  have hB : b%16=0 := by simpa [PairCongr,Int.ModEq] using hz.2
  cases e
  · rfl
  · have h : a%16=0 := by simpa [rotate,Int.ModEq] using he.2
    omega
  · have h : (-a)%16=9 := by simpa [rotate,Int.ModEq] using he.1
    omega
  · have h : b%16=9 := by simpa [rotate,Int.ModEq] using he.1
    omega

/-- The canonical oriented ray and its conjugate are distinct
already modulo 7, even though their adjacent norms are identical. -/
theorem conjugate_not_target {z : Pair} (hz : PairCongr 7 z (1,3)) :
    ¬PairCongr 7 (switch true z) (1,3) := by
  intro h
  have hb : z.2%7=3 := by simpa [Int.ModEq] using hz.2
  have hn : (-z.2)%7=3 := by simpa [switch,Int.ModEq] using h.2
  omega

structure Policy (s : ℕ) where
  base fresh : ℕ
  base16 : 16∣base
  base7 : 7∣base
  base51 : 51∣base
  covers : ∀ l : ℕ, l.Prime→l≠2→l≤s→l∣base ∨ l∣fresh

@[expose] def extraPrimes (base L₁ s : ℕ) : Finset ℕ :=
  (Finset.range (s+1)).filter fun l => l.Prime ∧ L₁<l ∧ ¬l∣base

@[expose] def extraModulus (base L₁ s : ℕ) : ℕ :=
  ∏ l∈extraPrimes base L₁ s,l

/-- Literal cutoff policy: base covers the preliminary small primes;
the new squarefree product covers exactly the rest that are needed. -/
def policy (base L₁ s : ℕ) (h16 : 16∣base) (h7 : 7∣base) (h51 : 51∣base)
    (hSmall : ∀ l : ℕ, l.Prime→l≠2→l≤L₁→l∣base) : Policy s where
  base := base
  fresh := extraModulus base L₁ s
  base16 := h16
  base7 := h7
  base51 := h51
  covers l hp h2 hs := by
    by_cases hl : l∣base
    · exact Or.inl hl
    · apply Or.inr
      have hLL : L₁<l := by
        by_contra H
        exact hl (hSmall l hp h2 (by omega))
      exact Finset.dvd_prod_of_mem (fun k => k)
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs),hp,hLL,hl⟩)

/-- The positive representative on the selected side of the unit
quotient, before choosing any actual Gaussian generator. -/
structure Reference {s : ℕ} (P : Policy s) (z : Pair) : Prop where
  ray16 : PairCongr 16 z (9,0)
  ray7 : PairCongr 7 z (1,3)
  rayI : ∀ l : ℕ, l.Prime→l≠2→l≠7→l∣P.base→PairCongr l z (0,1)
  fresh : ∀ l : ℕ, l.Prime→l∣P.fresh→Safe l z

/-- The ONLY class-field-facing input: one principal generator of a
degree-one prime (norm p), with the full-modulus associate relation
to one selected representative or its conjugate. It has no output
interval, sign or final obstruction certificate. -/
structure ArtinDatum {s : ℕ} (P : Policy s) (p : ℕ) where
  raw ref : Pair
  unit : Quarter
  bar : Bool
  rawNorm : norm raw=(p:ℤ)
  refGood : Reference P ref
  congr : PairCongr (P.base*P.fresh) (rotate unit raw) (switch bar ref)

@[expose] def normalize {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) : Pair :=
  switch D.bar (rotate D.unit D.raw)

theorem normalized_congr {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) :
    PairCongr (P.base*P.fresh) (normalize D) D.ref := by
  have h := switch_congr D.congr D.bar
  simpa only [switch_involutive,normalize] using h

theorem normalized_norm {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) :
    norm (normalize D)=(p:ℤ) := by
  rw [normalize,switch_norm,rotate_norm,D.rawNorm]

theorem base_into_full {s m : ℕ} (P : Policy s) (h : m∣P.base) : m∣P.base*P.fresh :=
  h.trans ⟨P.fresh,rfl⟩

theorem fresh_into_full {s m : ℕ} (P : Policy s) (h : m∣P.fresh) : m∣P.base*P.fresh :=
  h.trans ⟨P.base,Nat.mul_comm _ _⟩

theorem normalized_16 {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) :
    PairCongr 16 (normalize D) (9,0) :=
  pair_trans (reduce (normalized_congr D) (base_into_full P P.base16)) D.refGood.ray16

theorem normalized_7 {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) :
    PairCongr 7 (normalize D) (1,3) :=
  pair_trans (reduce (normalized_congr D) (base_into_full P P.base7)) D.refGood.ray7

theorem normalized_51 {s p : ℕ} {P : Policy s} (D : ArtinDatum P p) :
    PairCongr 51 (normalize D) (0,1) := by
  have h3 := D.refGood.rayI 3 (by decide) (by decide) (by decide)
    ((show 3∣51 by decide).trans P.base51)
  have h17 := D.refGood.rayI 17 (by decide) (by decide) (by decide)
    ((show 17∣51 by decide).trans P.base51)
  exact pair_trans (reduce (normalized_congr D) (base_into_full P P.base51)) (pair_51 h3 h17)

theorem normalized_small {s p : ℕ} {P : Policy s} (D : ArtinDatum P p)
    (l : ℕ) (hl : l.Prime) (h2 : l≠2) (hs : l≤s) : Safe l (normalize D) := by
  rcases P.covers l hl h2 hs with hb|hf
  · by_cases h7 : l=7
    · subst l
      exact safe_base_7 (normalized_7 D)
    · exact safe_base_i hl h2 (pair_trans
        (reduce (normalized_congr D) (base_into_full P hb)) (D.refGood.rayI l hl h2 h7 hb))
  · exact safe_transport (reduce (normalized_congr D) (fresh_into_full P hf))
      (D.refGood.fresh l hl hf)

/-- The physical prime stays in exactly the same annulus. Each real
coordinate is bounded by sqrt N; neither is forced positive. -/
theorem normalized_interval {s p N : ℕ} {P : Policy s} (D : ArtinDatum P p)
    (hlo : N≤2*p) (hhi : p≤N) :
    (N:ℝ)/2≤((normalize D).1:ℝ)^2+((normalize D).2:ℝ)^2 ∧
    ((normalize D).1:ℝ)^2+((normalize D).2:ℝ)^2≤(N:ℝ) ∧
    |((normalize D).1:ℝ)|≤Real.sqrt N ∧
    |((normalize D).2:ℝ)|≤Real.sqrt N := by
  have hn := normalized_norm D
  change (normalize D).1^2+(normalize D).2^2=(p:ℤ) at hn
  have hn' : ((normalize D).1:ℝ)^2+((normalize D).2:ℝ)^2=(p:ℝ) := by exact_mod_cast hn
  have hb : (p:ℝ)≤N := by exact_mod_cast hhi
  have ha : (N:ℝ)≤2*(p:ℝ) := by exact_mod_cast hlo
  refine ⟨by rw [hn']; linarith only [ha],hn'.trans_le hb,?_,?_⟩
  · rw [←Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith only [hn',hb,sq_nonneg ((normalize D).2:ℝ)])
  · rw [←Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith only [hn',hb,sq_nonneg ((normalize D).1:ℝ)])

end ActualGaussianRayConjugateLift318
