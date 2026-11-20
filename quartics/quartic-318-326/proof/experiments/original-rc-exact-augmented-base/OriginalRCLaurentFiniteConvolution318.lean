module
public import Mathlib.RingTheory.HahnSeries.PowerSeries
import Lean.Elab.Tactic.Omega

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCLaurentFiniteConvolution318

variable {R : Type*} [CommRing R]

/-- Exact convolution in the actual finite Laurent-coefficient ring. The
cutoff is a hypothesis on every out-of-window coefficient, not just on
Laurent terms sampled by the certificate. -/
theorem constant_product_window (L : ℕ) (F U : HahnSeries ℤ R)
    (hF : ∀ n : ℤ, n < -(L : ℤ) → F.coeff n = 0)
    (hU : ∀ n : ℤ, n < 0 → U.coeff n = 0) :
    (F*U).coeff 0 = F.coeff 0 * U.coeff 0 +
      ∑ j : Fin L, F.coeff (-((j.val : ℤ)+1)) * U.coeff ((j.val : ℤ)+1) := by
  classical
  let idxPair : Fin (L+1) → ℤ × ℤ := fun j => (-(j.val : ℤ), (j.val : ℤ))
  let W : Finset (ℤ × ℤ) := Finset.univ.image idxPair
  have ha : ∀ p ∈ Finset.antidiagonal F.isPWO_support U.isPWO_support (0:ℤ), p ∈ W := by
    intro p hp
    obtain ⟨hP,hQ,hs⟩ := Finset.mem_antidiagonal.mp hp
    have h₁ : -(L : ℤ) ≤ p.1 := by
      by_contra hh
      exact (HahnSeries.mem_support F p.1).mp hP (hF p.1 (lt_of_not_ge hh))
    have h₂ : 0 ≤ p.2 := by
      by_contra hh
      exact (HahnSeries.mem_support U p.2).mp hQ (hU p.2 (lt_of_not_ge hh))
    have ht : (p.2.toNat : ℤ) = p.2 := Int.toNat_of_nonneg h₂
    let j : Fin (L+1) := ⟨p.2.toNat, by omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
    apply Prod.ext
    · change -(p.2.toNat : ℤ) = p.1
      omega
    · exact ht
  have hb : ∀ p ∈ W, p ∉ Finset.antidiagonal F.isPWO_support U.isPWO_support (0:ℤ) →
      F.coeff p.1 * U.coeff p.2 = 0 := by
    intro p hp hn
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    by_cases h₁ : F.coeff (idxPair j).1 = 0
    · rw [h₁, zero_mul]
    by_cases h₂ : U.coeff (idxPair j).2 = 0
    · rw [h₂, mul_zero]
    exact (hn (Finset.mem_antidiagonal.mpr ⟨(HahnSeries.mem_support _ _).mpr h₁,
      (HahnSeries.mem_support _ _).mpr h₂, by simp [idxPair]⟩)).elim
  have hinj : Function.Injective idxPair := by
    intro i j h
    have he := congrArg Prod.snd h
    change (i.val : ℤ) = (j.val : ℤ) at he
    apply Fin.ext
    omega
  calc
    (F*U).coeff 0 = ∑ p ∈ Finset.antidiagonal F.isPWO_support U.isPWO_support (0:ℤ),
        F.coeff p.1 * U.coeff p.2 := HahnSeries.coeff_mul
    _ = ∑ p ∈ W, F.coeff p.1 * U.coeff p.2 := Finset.sum_subset ha hb
    _ = ∑ j : Fin (L+1), F.coeff (-(j.val : ℤ)) * U.coeff (j.val : ℤ) := by
      change (∑ p ∈ Finset.univ.image idxPair, F.coeff p.1 * U.coeff p.2) = _
      rw [Finset.sum_image (fun i _ j _ h => hinj h)]
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.cast_zero, neg_zero, Fin.val_succ, Nat.cast_succ]

/-- A genuinely regular power series embedded into the finite Laurent
ring has no negative coefficients, without needing a field coefficient. -/
theorem powerSeries_negative_zero (U : PowerSeries R) (n : ℤ) (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R U).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨i,hi⟩
  change (i : ℤ) = n at hi
  omega

/-- This is the exact finite cross-multiplied row required by V13
(5.11): c is the old denominator's valuation, not a support-token
valuation. It neither inverts two nor takes a constant of a ratio. -/
theorem scaled_constant_window (L : ℕ) (s : R) (F D : HahnSeries ℤ R)
    (U : PowerSeries R)
    (hF : ∀ n : ℤ, n < -(L : ℤ) → F.coeff n = 0)
    (hProd : HahnSeries.C s * D = F * HahnSeries.ofPowerSeries ℤ R U) :
    s * D.coeff 0 = F.coeff 0 * PowerSeries.constantCoeff U +
      ∑ j : Fin L, F.coeff (-((j.val : ℤ)+1)) * PowerSeries.coeff (j.val+1) U := by
  have h := congrArg (fun f : HahnSeries ℤ R => f.coeff 0) hProd
  change (HahnSeries.C s * D).coeff 0 = (F * HahnSeries.ofPowerSeries ℤ R U).coeff 0 at h
  have hlast := constant_product_window L F (HahnSeries.ofPowerSeries ℤ R U) hF
    (powerSeries_negative_zero U)
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hlast] at h
  have hzero : (HahnSeries.ofPowerSeries ℤ R U).coeff 0 = PowerSeries.constantCoeff U := by
    simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) U 0)
  have hplus (j : Fin L) : (HahnSeries.ofPowerSeries ℤ R U).coeff ((j.val : ℤ)+1) =
      PowerSeries.coeff (j.val+1) U := by
    rw [← Nat.cast_succ, HahnSeries.ofPowerSeries_apply_coeff]
  simpa only [hzero, hplus] using h

end OriginalRCLaurentFiniteConvolution318

#print axioms OriginalRCLaurentFiniteConvolution318.scaled_constant_window
