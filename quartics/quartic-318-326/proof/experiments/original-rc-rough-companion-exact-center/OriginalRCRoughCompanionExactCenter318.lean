module
public import OriginalRCNonzeroAddressBounds318
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

public section

namespace OriginalRCRoughCompanionExactCenter318

open OriginalRCNonzeroAddressBounds318
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem minus_one_valuation : (-1 : ℚ_[2]).valuation = 0 := by
  have h : ((-1 : ℚ_[2]) * (-1 : ℚ_[2])).valuation =
      (-1 : ℚ_[2]).valuation + (-1 : ℚ_[2]).valuation :=
    Padic.valuation_mul (by norm_num) (by norm_num)
  rw [show (-1 : ℚ_[2]) * (-1 : ℚ_[2]) = 1 by norm_num, Padic.valuation_one] at h
  omega

private theorem neg_valuation (x : ℚ_[2]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← neg_one_mul x, Padic.valuation_mul (by norm_num : (-1 : ℚ_[2]) ≠ 0) hx,
    minus_one_valuation, zero_add]

private theorem add_valuation_of_lt {x y : ℚ_[2]} (hy : y ≠ 0)
    (hxy : y.valuation < x.valuation) :
    x+y ≠ 0 ∧ (x+y).valuation = y.valuation := by
  have hn : x+y ≠ 0 := by
    intro h
    have he : x = -y := calc
      x = x+y-y := by ring
      _ = -y := by rw [h, zero_sub]
    rw [he, neg_valuation] at hxy
    exact (lt_irrefl _) hxy
  refine ⟨hn, le_antisymm ?_ ?_⟩
  · have he : (x+y)+(-x) = y := by ring
    have hn' : (x+y)+(-x) ≠ 0 := by rwa [he]
    have h := Padic.le_valuation_add hn'
    rw [he, neg_valuation] at h
    by_contra hf
    have hg : y.valuation < min (x+y).valuation x.valuation :=
      lt_min (lt_of_not_ge hf) hxy
    exact (not_lt_of_ge h) hg
  · simpa only [min_eq_right (le_of_lt hxy)] using Padic.le_valuation_add hn

/-- The two actual split moving quotients have this same scalar.
Apply it on each chosen finite stage before taking the inner limit
and before any uniform comparison. No cancellation in a finite ring. -/
theorem moving_prime_read (r a chi : ℚ_[2])
    (hchi : chi = 1 ∨ chi = -1) (hm : a-2*chi ≠ 0)
    (hdepth : (a-2*chi).valuation < (r-1).valuation) :
    r+1-chi*a ≠ 0 ∧ (r+1-chi*a).valuation = (a-2*chi).valuation := by
  have hsq : chi^2 = 1 := by
    rcases hchi with h | h <;> rw [h] <;> norm_num
  have hnchi : chi ≠ 0 := by
    rcases hchi with h | h <;> rw [h] <;> norm_num
  have hvchi : chi.valuation = 0 := by
    rcases hchi with h | h
    · rw [h, Padic.valuation_one]
    · rw [h, minus_one_valuation]
  have hs : (-(chi*(a-2*chi))).valuation = (a-2*chi).valuation := by
    rw [neg_valuation, Padic.valuation_mul hnchi hm, hvchi, zero_add]
  have he : r+1-chi*a = (r-1)+(-(chi*(a-2*chi))) := calc
    _ = (r-1)+(-(chi*(a-2*chi)))+(2-2*chi^2) := by ring
    _ = _ := by rw [hsq]; norm_num
  rw [he, ← hs]
  exact add_valuation_of_lt (neg_ne_zero.mpr (mul_ne_zero hnchi hm)) (by rwa [hs])

/-- The marked coordinate is literally the older ordinary Kummer row C.
The remaining classical equality is the Milne ratio for the actual same
A=Res and B=product, after evaluating g_B=4, period valuation 1,
regulator valuation 1-2*v₂(I), and the component contribution 2 per q|k.
The central identity is not an asserted definition of C. -/
theorem read_after_same_milne {x : ℚ_[2]} (C : MarkedCentralRow x)
    (s sComp omegaComp valI : ℕ)
    (hmoving : C.movingLength = 2*C.movingScalarVal)
    (hSha : (C.shaLength:ℤ) - s - sComp =
      2*(C.g:ℤ)-8+(1-2*(valI:ℤ))+1+2*omegaComp) :
    x ≠ 0 ∧ x.valuation =
      C.basisShift+2*(C.jRC:ℤ)-4*C.omega-s-sComp-2*omegaComp+
        2*C.Lval+6+2*valI := by
  obtain ⟨hne, hv⟩ := C.read
  exact ⟨hne, by omega⟩

/-- Strict root-order margin for the same center. It keeps the helpful
+2*omegaComp lower-index term. valI≤1 is the actual rank-one consequence
of IJ=2; old is a fixed upper bound of the retained basis contribution.
The external outer argument only supplies the bound on THIS x. -/
theorem strict_same_marked_lower {x : ℚ_[2]} (C : MarkedCentralRow x)
    (s sComp omegaComp valI cU ell : ℕ) (old : ℤ)
    (hmoving : C.movingLength = 2*C.movingScalarVal)
    (hSha : (C.shaLength:ℤ) - s - sComp =
      2*(C.g:ℤ)-8+(1-2*(valI:ℤ))+1+2*omegaComp)
    (hI : valI ≤ 1) (hL : C.Lval ≤ ell) (hOld : C.basisShift ≤ old)
    (hOuter : -(cU:ℤ) ≤ x.valuation) :
    4*(C.omega:ℤ)+s+sComp+2*omegaComp -
      ((cU:ℤ)+old+2*ell+9) < 2*(C.jRC:ℤ) := by
  obtain ⟨_, hv⟩ := read_after_same_milne C s sComp omegaComp valI hmoving hSha
  omega

end OriginalRCRoughCompanionExactCenter318

#print axioms OriginalRCRoughCompanionExactCenter318.moving_prime_read
#print axioms OriginalRCRoughCompanionExactCenter318.strict_same_marked_lower
