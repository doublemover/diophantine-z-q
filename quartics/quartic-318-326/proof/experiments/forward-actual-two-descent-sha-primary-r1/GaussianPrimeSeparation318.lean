module
public import GaussianQuarterModuli318
public import OrderSeparation
public section
noncomputable section
namespace GaussianPrimeSeparation318
open GaussianNeighborNorms318 GaussianQuarterModuli318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)

include hv in
lemma value_cast (k : ℤ) (hk : k∈coefficients C) :
    ((value u w k).natAbs:ℝ)=(value u w k:ℝ) := by
  exact_mod_cast (Int.natCast_natAbs (value u w k)).trans (abs_of_pos (hv.positive k hk))

include hv in
/-- Distinct MERGED coefficients give spacing at least w²; duplicate
original positions are deliberately not treated as distinct primes. -/
lemma spacing (k l : ℤ) (hk : k∈coefficients C) (hl : l∈coefficients C) (hne : k≠l) :
    (w:ℝ)^2≤|((value u w k).natAbs:ℝ)-((value u w l).natAbs:ℝ)| := by
  have hi : 1≤|k-l| := by have hh := abs_pos.mpr (sub_ne_zero.mpr hne); omega
  have hr : (1:ℝ)≤|(k:ℝ)-(l:ℝ)| := by exact_mod_cast hi
  rw [value_cast C u w hv k hk,value_cast C u w hv l hl]
  have he : (value u w k:ℝ)-(value u w l:ℝ)=((k:ℝ)-(l:ℝ))*(w:ℝ)^2 := by
    simp only [ClearedContactForms318.value,Int.cast_add,Int.cast_mul,Int.cast_pow]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg (w:ℝ))]
  nlinarith [sq_nonneg (w:ℝ)]

include hv in
/-- The actual finite separation argument uses a common error/range bound
and exact source spacing. These finite growth inputs remain for PP to supply. -/
theorem separated (a b : Fin 3 × Fin 5 → ℤ)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (E : ℝ) (herror : ∀ i, 1+2*|(a i:ℝ)|≤E) (hspace : E<(w:ℝ)^2)
    (hrange : ∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5,
      ((row C u w i.1 i.2).natAbs:ℝ)+E<2*((value u w k).natAbs:ℝ)) :
    ∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5, ¬(value u w k).natAbs∣plus (a i) (b i) := by
  intro k hk i
  let p := (value u w k).natAbs
  let q := (row C u w i.1 i.2).natAbs
  letI : Fact q.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  let d := plus (a i) (b i)
  have hp : 0<p := (hv.prime k hk).pos
  obtain ⟨m,n,hm,hn,hminus,hplus⟩ := ray_factors (a i) (b i) (hray i).2.1 (hray i).2.2
  have hd : 0<d := by dsimp [d]; rw [hplus]; have hnpos := odd_pos hn; positivity
  have hdeven : Even d := by refine ⟨2*n,?_⟩; dsimp [d]; rw [hplus]; ring
  have herr : |(d:ℝ)-(q:ℝ)|≤E := by
    have hid : (d:ℝ)-(q:ℝ)=1+2*(a i:ℝ) := by
      exact_mod_cast (neighbor_errors _ (a i) (b i) (hray i).1).2
    rw [hid]
    calc
      |1+2*(a i:ℝ)|≤|1|+|2*(a i:ℝ)| := abs_add_le _ _
      _ = 1+2*|(a i:ℝ)| := by rw [abs_mul]; norm_num
      _ ≤ E := herror i
  have hbound : d<2*p := by
    have hh := (abs_le.mp herr).2
    have hR := hrange k hk i
    have he : (d:ℝ)<2*(p:ℝ) := by dsimp [p,q] at *; linarith
    exact_mod_cast he
  by_cases he : k=C.coefficient i
  · have hpq : p=q := by dsimp [p,q,row]; rw [he]
    have hpodd : Odd p := by
      have hmod := GaussianRayQuadratic318.prime_mod q (a i) (b i) (hray i)
      refine ⟨p/2,?_⟩
      omega
    exact OrderSeparation.diagonal_not_dvd p d hp hd hbound hpodd hdeven
  · apply OrderSeparation.off_diagonal_not_dvd p q d E hp hd hbound herr
    exact hspace.trans_le (spacing C u w hv k (C.coefficient i) hk (coefficient_mem C i) he)

include hv in
/-- No selected-prime divisor is introduced by the actual all15 quarter
LCM. Its index set stays separate from the merged product index set. -/
theorem product_coprime_upper (a b : Fin 3 × Fin 5 → ℤ)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (E : ℝ) (herror : ∀ i, 1+2*|(a i:ℝ)|≤E) (hspace : E<(w:ℝ)^2)
    (hrange : ∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5,
      ((row C u w i.1 i.2).natAbs:ℝ)+E<2*((value u w k).natAbs:ℝ)) :
    Nat.Coprime (product C u w) (upper a b) := by
  apply PrimeCRTAssembly.product_coprime_lcm (coefficients C) Finset.univ
    (fun k => (value u w k).natAbs) (fun i => plus (a i) (b i)) (fun i => plus (a i) (b i)/4)
  · exact hv.prime
  · exact fun k hk i hi => separated C u w hv a b hray E herror hspace hrange k hk i
  · intro i hi
    obtain ⟨m,n,hm,hn,he,hf⟩ := ray_factors (a i) (b i) (hray i).2.1 (hray i).2.2
    have hq : plus (a i) (b i)/4=n := by omega
    rw [hq,hf]
    exact dvd_mul_left _ _

include hv in
/-- A fixed prime cutoff exceeding L supplies the other selected-product
coprimality. No avoidance of the later variable w is assumed. -/
theorem product_coprime_continuity (L : ℕ) (hL : 0<L)
    (hlarge : ∀ k∈coefficients C, L<(value u w k).natAbs) : Nat.Coprime (product C u w) L := by
  apply Nat.coprime_prod_left_iff.mpr
  intro k hk
  exact Nat.coprime_of_lt_prime (Nat.ne_of_gt hL) (hlarge k hk) (hv.prime k hk)


end GaussianPrimeSeparation318
