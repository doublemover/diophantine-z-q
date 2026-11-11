module
public import ActualHalfPointLift318
public section
noncomputable section
namespace SelectedQuarterOrder318
open ConcretePadic318 SelectedReductionOrder318 GoodReductionResidue318
open ReciprocalDouble318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- Actual quarter-count divisibility of the original R-class, produced
from the precise extra residue root data in the historical ray argument. -/
theorem actual_order_dvd_quarter (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2) (h7 : ¬p∣49)
    (z t : ZMod p) (hz : z^8= -1) (ht : t^4=2) :
    SelectedQuotientOrders318.order p rho hr∣pointCount p rho hr/4 := by
  let d := coefficient p rho hr
  let r : ℤ_[p] := ⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩
  let a : ℤ_[p] := 3-r
  have hd : d=a^2 := by
    apply Subtype.ext
    exact ActualSplitOrbitEntry318.coefficient_eq p rho hr
  have ha : ‖a‖=1 := by
    have he := coefficient_unit p rho hr h7
    change ‖d‖=1 at he
    rw [hd,norm_pow] at he
    nlinarith [norm_nonneg a]
  obtain ⟨Q,hQ⟩ := ActualHalfPointLift318.original_half p rho hr hp z t hz ht
  have he := ActualFourTorsion318.doubled_order_dvd_quarter_of_square p hp d a ha hd Q
  rw [hQ] at he
  change SelectedQuotientOrders318.order p rho hr∣(1+Nat.card (ResidueCurve p d))/4 at he
  dsimp only [d] at he
  simpa only [pointCount,ResidueCurve,residue_coefficient] using he

open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318

/-- Exactly the two finite roots used by the historical halving argument,
at every original selected prime position. Their Gaussian ray production
and CM count are not asserted in this structure. -/
@[expose] def RootData {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ)
    (hv : Values C u w) : Prop := ∀ i : Fin 3 × Fin 5,
  let p := (row C u w i.1 i.2).natAbs
  ∃ z t : ZMod p, z^8= -1 ∧ t^4=2

/-- The original actual moduli now divide the quarter-count LCMs at all15
primary/conjugate positions. Same finite roots work for both signs of rho. -/
theorem actual_moduli_dvd_quarters {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ)
    (hv : Values C u w) (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5, 49<(row C u w i.1 i.2).natAbs)
    (hroots : RootData C u w hv) :
    minus C u w hv r∣Finset.univ.lcm (fun i => counts C u w hv r false i/4) ∧
    plus C u w hv r∣Finset.univ.lcm (fun i => counts C u w hv r true i/4) := by
  apply divides_proposed C u w hv r
  · intro i
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    have hp : p≠2 := by have hh := hlarge i; omega
    have h7 : ¬p∣49 := by
      intro hd
      have hh := Nat.le_of_dvd (by norm_num : 0<49) hd
      have hl := hlarge i
      omega
    obtain ⟨z,t,hz,ht⟩ := hroots i
    exact (actual_order_dvd_quarter p (r i).val (r i).property hp h7 z t hz ht).trans
      (show counts C u w hv r false i/4∣Finset.univ.lcm (fun k => counts C u w hv r false k/4) from
        Finset.dvd_lcm (Finset.mem_univ i))
  · intro i
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    have hp : p≠2 := by have hh := hlarge i; omega
    have h7 : ¬p∣49 := by
      intro hd
      have hh := Nat.le_of_dvd (by norm_num : 0<49) hd
      have hl := hlarge i
      omega
    obtain ⟨z,t,hz,ht⟩ := hroots i
    exact (actual_order_dvd_quarter p (-(r i).val) (negative_root p (r i).val (r i).property)
      hp h7 z t hz ht).trans
      (show counts C u w hv r true i/4∣Finset.univ.lcm (fun k => counts C u w hv r true k/4) from
        Finset.dvd_lcm (Finset.mem_univ i))

end SelectedQuarterOrder318
