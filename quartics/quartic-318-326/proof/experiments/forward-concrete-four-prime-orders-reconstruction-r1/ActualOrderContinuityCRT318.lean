module
public import ExactContinuityDivisibilityCRT318
public section
noncomputable section
namespace ActualOrderContinuityCRT318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- The same original prime product and two actual fifteen-position order LCMs are consumed. -/
theorem compatible_iff (r : Roots C u w hv) (L h0 : ℕ)
    (hPm : Nat.Coprime (product C u w) (plus C u w hv r))
    (hmp : Nat.Coprime (minus C u w hv r) (plus C u w hv r))
    (hpL : Nat.Coprime (plus C u w hv r) L) :
    (∃ h : ℕ, Nat.ModEq ((product C u w)^3*minus C u w hv r) h 0 ∧
      Nat.ModEq (plus C u w hv r) h 1 ∧ Nat.ModEq L h h0) ↔
      Nat.gcd ((product C u w)^3*minus C u w hv r) L∣h0 :=
  ExactContinuityDivisibilityCRT318.compatible_iff _ _ _ _ _ _ hPm hmp hpL
/-- Orders and actual root assignment accompany the compatible residues at the SAME index.
The coprimalities, continuity test and simultaneous-prime Values remain explicit inputs. -/
theorem witness (r : Roots C u w hv) (L h0 : ℕ)
    (hPm : Nat.Coprime (product C u w) (plus C u w hv r))
    (hmp : Nat.Coprime (minus C u w hv r) (plus C u w hv r))
    (hpL : Nat.Coprime (plus C u w hv r) L)
    (hc : Nat.gcd ((product C u w)^3*minus C u w hv r) L∣h0) :
    ∃ h : ℕ, Nat.ModEq ((product C u w)^3*minus C u w hv r) h 0 ∧
      Nat.ModEq (plus C u w hv r) h 1 ∧ Nat.ModEq L h h0 ∧
      SelectedTraceFromOrders318.Orders C u w hv (minus C u w hv r) (plus C u w hv r) := by
  obtain ⟨h,hA,hP,hL⟩ := (compatible_iff C u w hv r L h0 hPm hmp hpL).mpr hc
  exact ⟨h,hA,hP,hL,orders C u w hv r⟩
end ActualOrderContinuityCRT318
