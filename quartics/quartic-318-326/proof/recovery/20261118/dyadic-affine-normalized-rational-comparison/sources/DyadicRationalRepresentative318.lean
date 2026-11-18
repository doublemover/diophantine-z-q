module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic
public section
namespace DyadicRationalRepresentative318

@[expose] def Rep (r : ℤ) : Prop := r=1 ∨ r= -1 ∨ r=2 ∨ r= -2

private theorem negRep {r : ℤ} (hr : Rep r) : Rep (-r) := by
  rcases hr with h|h|h|h <;> subst r <;> norm_num [Rep]

/-- Strip powers of four, not powers of two: the terminal eight residues
produce exactly one of the signed valuation-parity representatives. -/
theorem natural_decomposition (n : ℕ) (hn : n≠0) :
    ∃ r c : ℤ, ∃ j : ℕ, Rep r ∧ (n:ℤ)=r*(1+4*c)*((2:ℤ)^j)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hd : n%4=0
    · obtain ⟨r,c,j,hr,he⟩ := ih (n/4) (by omega) (by omega)
      refine ⟨r,c,j+1,hr,?_⟩
      have hn' : (n:ℤ)=4*((n/4:ℕ):ℤ) := by omega
      rw [hn',he,pow_succ]; ring
    · by_cases h1 : (n:ℤ)%4=1
      · exact ⟨1,((n:ℤ)-1)/4,0,by norm_num [Rep],by norm_num <;> omega⟩
      by_cases h3 : (n:ℤ)%4=3
      · exact ⟨-1,(-(n:ℤ)-1)/4,0,by norm_num [Rep],by norm_num <;> omega⟩
      by_cases h2 : (n:ℤ)%8=2
      · exact ⟨2,((n:ℤ)-2)/8,0,by norm_num [Rep],by norm_num <;> omega⟩
      exact ⟨-2,(-(n:ℤ)-2)/8,0,by norm_num [Rep],by norm_num <;> omega⟩

theorem integer_decomposition (n : ℤ) (hn : n≠0) :
    ∃ r c : ℤ, ∃ j : ℕ, Rep r ∧ n=r*(1+4*c)*((2:ℤ)^j)^2 := by
  cases n with
  | ofNat m =>
    exact natural_decomposition m (by omega)
  | negSucc m =>
    obtain ⟨r,c,j,hr,he⟩ := natural_decomposition (m+1) (by omega)
    refine ⟨-r,c,j,negRep hr,?_⟩
    have he' : Int.negSucc m = -((m+1:ℕ):ℤ) := by omega
    rw [he',he]; ring

/-- Arbitrary nonzero rational coefficient, not an assumed local squareclass:
an actual rational nonzero scale and an integral 1 mod 4 residual unit. -/
theorem rational_decomposition (q : ℚ) (hq : q≠0) :
    ∃ (r c : ℤ) (v : ℚ), Rep r ∧ v≠0 ∧ q=(r:ℚ)*(1+4*(c:ℚ))*v^2 := by
  have hd : (q.den:ℚ)≠0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  obtain ⟨r,c,j,hr,he⟩ := integer_decomposition (q.num*(q.den:ℤ))
    (mul_ne_zero (Rat.num_ne_zero.mpr hq) (Nat.cast_ne_zero.mpr q.den_ne_zero))
  refine ⟨r,c,(2:ℚ)^j/(q.den:ℚ),hr,div_ne_zero (pow_ne_zero j (by norm_num)) hd,?_⟩
  have he' : (q.num:ℚ)*(q.den:ℚ) = (r:ℚ)*(1+4*(c:ℚ))*((2:ℚ)^j)^2 := by exact_mod_cast he
  calc
    q = (q.num:ℚ)/(q.den:ℚ) := q.num_div_den.symm
    _ = ((q.num:ℚ)*(q.den:ℚ))/(q.den:ℚ)^2 := by field_simp <;> ring
    _ = (r:ℚ)*(1+4*(c:ℚ))*((2:ℚ)^j/(q.den:ℚ))^2 := by rw [he',div_pow]; ring

/-- The residual factor is actually invertible at every local point over two. -/
theorem residual_unit {R : Type*} [CommRing R] [IsLocalRing R]
    (h2 : (2:R) ∈ IsLocalRing.maximalIdeal R) (c : R) : IsUnit (1+4*c) := by
  by_contra h
  have hh : 1+4*c ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff] using h
  have h1 : (1:R) ∈ IsLocalRing.maximalIdeal R := by
    have hm := (IsLocalRing.maximalIdeal R).mul_mem_left (2*c) h2
    convert (IsLocalRing.maximalIdeal R).sub_mem hh hm using 1 <;> ring
  have hn : ¬IsUnit (1:R) := by
    simpa only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff] using h1
  exact hn isUnit_one

end DyadicRationalRepresentative318
