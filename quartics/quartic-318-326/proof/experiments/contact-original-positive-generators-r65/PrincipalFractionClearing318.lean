module
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Fintype.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section
noncomputable section
namespace PrincipalFractionClearing318
open scoped BigOperators
set_option maxHeartbeats 600000
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The actual localization at a nonzero principal element, inside the fraction field. -/
abbrev away (f : R) (hf : f ≠ 0) : Subalgebra R K :=
  Localization.subalgebra.ofField K (Submonoid.powers f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem mem_away_iff (f : R) (hf : f ≠ 0) (x : K) :
    x ∈ away f hf ↔ ∃ (n : ℕ) (a : R), x = algebraMap R K a / algebraMap R K f ^ n := by
  change (∃ a s : R, ∃ hs : s ∈ Submonoid.powers f,
    x = algebraMap R K a * (algebraMap R K s)⁻¹) ↔ _
  constructor
  · rintro ⟨a,s,⟨n,rfl⟩,h⟩
    exact ⟨n,a,by simpa only [map_pow, div_eq_mul_inv] using h⟩
  · rintro ⟨n,a,h⟩
    exact ⟨a,f^n,⟨n,rfl⟩,by simpa only [map_pow, div_eq_mul_inv] using h⟩

/-- Multiplying by a sufficiently large power of the second denominator clears it,
leaving a genuine section over the first principal open. -/
theorem clear_second (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (x : K) (hx : x ∈ away (f*g) (mul_ne_zero hf hg)) :
    ∃ n : ℕ, algebraMap R K g ^ n * x ∈ away f hf := by
  obtain ⟨n,a,rfl⟩ := (mem_away_iff _ _ _).mp hx
  refine ⟨n,(mem_away_iff _ _ _).mpr ⟨n,a,?_⟩⟩
  have hf' : algebraMap R K f ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hf
  have hg' : algebraMap R K g ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hg
  rw [map_mul,mul_pow]
  field_simp

theorem clear_second_of_le (f g : R) (hf : f ≠ 0) {n N : ℕ} (hn : n ≤ N)
    (x : K) (hx : algebraMap R K g ^ n * x ∈ away f hf) :
    algebraMap R K g ^ N * x ∈ away f hf := by
  have h := (away (K:=K) f hf).mul_mem
    ((away f hf).algebraMap_mem (g ^ (N-n))) hx
  simpa only [map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn] using h

/-- One exponent clears every second denominator of an actual finite overlap family. -/
theorem clear_finite {ι : Type*} [Fintype ι] (f : ι → R) (hf : ∀ i, f i ≠ 0)
    (c : ι → ι → K)
    (hc : ∀ i j, c i j ∈ away (f i * f j) (mul_ne_zero (hf i) (hf j))) :
    ∃ N : ℕ, ∀ i j, algebraMap R K (f j) ^ N * c i j ∈ away (f i) (hf i) := by
  choose n hn using fun i j => clear_second (f i) (f j) (hf i) (hf j) (c i j) (hc i j)
  let N := ⨆ i, ⨆ j, n i j
  refine ⟨N,fun i j => clear_second_of_le (f i) (f j) (hf i) ?_ _ (hn i j)⟩
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (Finite.bddAbove_range _) j)

end PrincipalFractionClearing318
