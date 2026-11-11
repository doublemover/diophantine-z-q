module
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Tactic
public section
noncomputable section
namespace WeightedMonicRootBound318
open Polynomial

/-- Cauchy's actual root bound with a common positive pole weight.
Only coefficients below the exact monic degree are needed. -/
theorem root_bound (p : Polynomial ℂ) (hm : p.Monic) (δ A : ℝ)
    (hδ : 0 < δ) (hA : 0 ≤ A)
    (hc : ∀ n < p.natDegree, δ * ‖p.coeff n‖ ≤ A)
    (z : ℂ) (hz : p.IsRoot z) : δ * ‖z‖ ≤ A + δ := by
  let C : ℝ≥0 := ⟨A/δ,div_nonneg hA hδ.le⟩
  have hcoeff (n : ℕ) (hn : n ∈ Finset.range p.natDegree) : ‖p.coeff n‖₊ ≤ C := by
    have hn' := hc n (Finset.mem_range.mp hn)
    have hh : ‖p.coeff n‖ ≤ A/δ := (le_div_iff₀ hδ).mpr (by simpa [mul_comm] using hn')
    exact_mod_cast hh
  have hsup : (Finset.range p.natDegree).sup (fun n => ‖p.coeff n‖₊) ≤ C :=
    Finset.sup_le hcoeff
  have hcb : p.cauchyBound ≤ C+1 := by
    simpa only [Polynomial.cauchyBound,hm.leadingCoeff,nnnorm_one,div_one] using
      add_le_add_right hsup 1
  have hroot := (hz.norm_lt_cauchyBound hm.ne_zero).le.trans hcb
  have hreal : ‖z‖ ≤ A/δ+1 := by exact_mod_cast hroot
  calc
    δ * ‖z‖ ≤ δ * (A/δ+1) := mul_le_mul_of_nonneg_left hreal hδ.le
    _ = A+δ := by field_simp [ne_of_gt hδ]; ring
end WeightedMonicRootBound318
