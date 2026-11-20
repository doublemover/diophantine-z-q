module
public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.RingTheory.ClassGroup.Basic
public section
noncomputable section

namespace ActualCMLatticeDualOrientation318

/-- Forward analytic quotient-group arrow for the actual nested lattices. -/
@[expose] def forward (A B : AddSubgroup ℂ) (hAB : A ≤ B) :
    (ℂ ⧸ A) →+ (ℂ ⧸ B) :=
  QuotientAddGroup.map A B (AddMonoidHom.id ℂ) (by simpa only [AddSubgroup.comap_id] using hAB)

theorem forward_kernel (A B : AddSubgroup ℂ) (hAB : A ≤ B) :
    (forward A B hAB).ker = B.map (QuotientAddGroup.mk' A) := by
  simp only [forward, QuotientAddGroup.ker_map, AddSubgroup.comap_id]

@[expose] def natScale (N : ℕ) : ℂ →+ ℂ := nsmulAddMonoidHom (α := ℂ) N

/-- The normalized target A/N, as a preimage under actual multiplication N. -/
@[expose] def normalizedTarget (A : AddSubgroup ℂ) (N : ℕ) : AddSubgroup ℂ :=
  A.comap (natScale N)

@[expose] def dual (A B : AddSubgroup ℂ) (N : ℕ) (hNB : B ≤ normalizedTarget A N) :
    (ℂ ⧸ B) →+ (ℂ ⧸ A) :=
  QuotientAddGroup.map B A (natScale N) hNB

@[expose] def rescaleTarget (A : AddSubgroup ℂ) (N : ℕ) :
    (ℂ ⧸ normalizedTarget A N) →+ (ℂ ⧸ A) :=
  QuotientAddGroup.map (normalizedTarget A N) A (natScale N) le_rfl

/-- Explicit inverse scaling of a quotient representative makes the
normalization an actual group isomorphism, not multiplication by N
inside a fixed torus. -/
theorem rescaleTarget_bijective (A : AddSubgroup ℂ) (N : ℕ) (hN : N ≠ 0) :
    Function.Bijective (rescaleTarget A N) := by
  constructor
  · apply (AddMonoidHom.ker_eq_bot_iff _).mp
    change (QuotientAddGroup.map (normalizedTarget A N) A (natScale N) le_rfl).ker = ⊥
    rw [QuotientAddGroup.ker_map]
    exact QuotientAddGroup.map_mk'_self (normalizedTarget A N)
  · intro P
    obtain ⟨z, rfl⟩ := (QuotientAddGroup.mk'_surjective A) P
    have hz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    refine ⟨QuotientAddGroup.mk' (normalizedTarget A N) ((N : ℂ)⁻¹ * z), ?_⟩
    change QuotientAddGroup.mk' A (N • ((N : ℂ)⁻¹ * z)) = QuotientAddGroup.mk' A z
    apply congrArg (QuotientAddGroup.mk' A)
    rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem dual_after_forward (A B : AddSubgroup ℂ) (hAB : A ≤ B) (N : ℕ)
    (hNB : B ≤ normalizedTarget A N) (P : ℂ ⧸ A) :
    dual A B N hNB (forward A B hAB P) = N • P := by
  obtain ⟨z, rfl⟩ := (QuotientAddGroup.mk'_surjective A) P
  change QuotientAddGroup.mk' A (N • z) = N • QuotientAddGroup.mk' A z
  exact map_nsmul (QuotientAddGroup.mk' A) z N

theorem forward_after_dual (A B : AddSubgroup ℂ) (hAB : A ≤ B) (N : ℕ)
    (hNB : B ≤ normalizedTarget A N) (P : ℂ ⧸ B) :
    forward A B hAB (dual A B N hNB P) = N • P := by
  obtain ⟨z, rfl⟩ := (QuotientAddGroup.mk'_surjective B) P
  change QuotientAddGroup.mk' B (N • z) = N • QuotientAddGroup.mk' B z
  exact map_nsmul (QuotientAddGroup.mk' B) z N

/-- The reversed cyclic arrow, by identity on ℂ, has source B and
target A/N. It is the dual after the exact target rescaling. -/
theorem dual_as_rescaled_reverse (A B : AddSubgroup ℂ) (N : ℕ)
    (hNB : B ≤ normalizedTarget A N) :
    dual A B N hNB =
      (rescaleTarget A N).comp (forward B (normalizedTarget A N) hNB) := by
  apply AddMonoidHom.ext
  intro P
  obtain ⟨z, rfl⟩ := (QuotientAddGroup.mk'_surjective B) P
  rfl

open scoped nonZeroDivisors

abbrev FractionalUnit (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ

/-- On actual fractional ideals, B = a·𝔫⁻¹ and its reversed
overlattice B·𝔫̄⁻¹ is a·(N)⁻¹. The first label of the dual
has the inverse shift, and conjugation therefore preindexes by
A⁻¹[𝔫], not A⁻¹[𝔫]⁻¹ in this source-lattice convention. -/
theorem literal_ideal_dual_orientation (K : Type*) [Field K] [NumberField K]
    (a 𝔫 𝔫bar principalN : FractionalUnit K) (hsplit : 𝔫 * 𝔫bar = principalN) :
    (a * 𝔫⁻¹) * 𝔫bar⁻¹ = a * principalN⁻¹ ∧
    ClassGroup.mk K (a * 𝔫⁻¹) = ClassGroup.mk K a * (ClassGroup.mk K 𝔫)⁻¹ ∧
    ClassGroup.mk K ((a⁻¹ * 𝔫) * 𝔫⁻¹) = (ClassGroup.mk K a)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = a * (𝔫bar * 𝔫)⁻¹ := by rw [mul_assoc, mul_inv_rev]
      _ = _ := by rw [mul_comm 𝔫bar 𝔫, hsplit]
  · rw [map_mul, map_inv]
  · simp [mul_assoc]

end ActualCMLatticeDualOrientation318
