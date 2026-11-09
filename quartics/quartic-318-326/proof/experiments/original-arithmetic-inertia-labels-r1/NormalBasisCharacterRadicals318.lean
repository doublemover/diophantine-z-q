module
public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.Tactic
public section
noncomputable section
open scoped BigOperators
namespace NormalBasisCharacterRadicals318
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- A Fourier sum of the ORIGINAL Galois orbit basis inside the given field. -/
@[expose] def root (χ : (L ≃ₐ[F] L) →* F) : L :=
  ∑ g : L ≃ₐ[F] L, χ g • IsGalois.normalBasis F L g

lemma root_coordinate_one (χ : (L ≃ₐ[F] L) →* F) :
    (IsGalois.normalBasis F L).repr (root χ) 1 = 1 := by
  classical
  simp [root, map_sum, map_smul]

/-- Nonvanishing is proved by an actual basis coordinate, not asserted from a
character name or a formal averaging operator. -/
theorem root_ne_zero (χ : (L ≃ₐ[F] L) →* F) : root χ ≠ 0 := by
  intro h
  have hc := root_coordinate_one χ
  rw [h, map_zero, Finsupp.zero_apply] at hc
  exact zero_ne_one hc

lemma basis_action (σ g : L ≃ₐ[F] L) :
    σ (IsGalois.normalBasis F L g) = IsGalois.normalBasis F L (σ * g) := by
  rw [IsGalois.normalBasis_apply g, IsGalois.normalBasis_apply (σ * g)]
  all_goals rfl

/-- Reindexing the genuine orbit computes the supplied order-two character. -/
theorem root_action (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1)
    (σ : L ≃ₐ[F] L) : σ (root χ) = χ σ • root χ := by
  classical
  calc
    σ (root χ) = ∑ g : L ≃ₐ[F] L, χ g • IsGalois.normalBasis F L (σ * g) := by
      simp only [root, map_sum, map_smul, basis_action]
    _ = χ σ • ∑ g : L ≃ₐ[F] L, χ (σ * g) • IsGalois.normalBasis F L (σ * g) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [map_mul, smul_smul, ← mul_assoc, ← pow_two, hχ, one_mul]
    _ = χ σ • root χ := by
      congr 1
      exact (Equiv.mulLeft σ).sum_comp
        (fun g : L ≃ₐ[F] L => χ g • IsGalois.normalBasis F L g)

/-- Squaring the constructed character vector really descends through the
ORIGINAL fixed-field theorem to the original base field. -/
theorem square_in_base (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1) :
    ∃ a : F, algebraMap F L a = root χ ^ 2 := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  rw [map_pow, root_action χ hχ, Algebra.smul_def, mul_pow, ← map_pow, hχ, map_one, one_mul]

@[expose] def radicand (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1) : F :=
  (square_in_base χ hχ).choose

theorem root_square (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1) :
    root χ ^ 2 = algebraMap F L (radicand χ hχ) :=
  (square_in_base χ hχ).choose_spec.symm

theorem radicand_ne_zero (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1) :
    radicand χ hχ ≠ 0 := by
  intro h
  have hz := root_square χ hχ
  rw [h, map_zero] at hz
  exact pow_ne_zero 2 (root_ne_zero χ) hz

/-- The constructed element is genuinely quadratic for a nontrivial sign
character, rather than merely a possibly split root polynomial. -/
theorem radicand_nonsquare (χ : (L ≃ₐ[F] L) →* F) (hχ : ∀ g, χ g ^ 2 = 1)
    (hne : ∃ σ, χ σ ≠ 1) : ¬ IsSquare (radicand χ hχ) := by
  intro hs
  obtain ⟨a, ha⟩ := (isSquare_iff_exists_sq _).mp hs
  have hr : root χ ^ 2 = (algebraMap F L a) ^ 2 := by
    rw [root_square, ha, map_pow]
  have hf : ∀ σ : L ≃ₐ[F] L, σ (root χ) = root χ := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hr with h | h
    · intro σ
      rw [h, σ.commutes]
    · intro σ
      rw [h, map_neg, σ.commutes]
  obtain ⟨σ, hσ⟩ := hne
  apply hσ
  apply (algebraMap F L).injective
  have he := (root_action χ hχ σ).symm.trans (hf σ)
  rw [Algebra.smul_def] at he
  simpa only [map_one] using mul_right_cancel₀ (root_ne_zero χ)
    (he.trans (one_mul (root χ)).symm)
end NormalBasisCharacterRadicals318
