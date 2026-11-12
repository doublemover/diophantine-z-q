module
public import GoodReductionCardinality318
public section
noncomputable section
namespace SelectedReductionOrder318
open ConcretePadic318 GoodReductionResidue318 GoodReductionLifting318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def coefficient (rho : ℚ_[p]) (hr : rho^2=2) : ℤ_[p] :=
  ⟨embedding p rho hr ConcreteG8Domain.D,ActualSplitOrbitEntry318.coefficient_integral p rho hr⟩

lemma coefficient_unit (rho : ℚ_[p]) (hr : rho^2=2) (h7 : ¬p∣49) :
    ‖coefficient p rho hr‖=1 := by
  have he := ActualReciprocalParameters318.coefficient_unit p rho hr h7
  have hn := ActualSplitOrbitEntry318.coefficient_ne p rho hr
  change Padic.addValuation (embedding p rho hr ConcreteG8Domain.D)=0 at he
  rw [Padic.addValuation.apply hn] at he
  have hv : (embedding p rho hr ConcreteG8Domain.D).valuation=0 := by exact_mod_cast he
  change ‖embedding p rho hr ConcreteG8Domain.D‖=1
  rw [Padic.norm_eq_zpow_neg_valuation hn,hv,neg_zero,zpow_zero]

@[expose] def residueRoot (rho : ℚ_[p]) (hr : rho^2=2) : ZMod p :=
  PadicInt.toZMod (⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩:ℤ_[p])

lemma residueRoot_square (rho : ℚ_[p]) (hr : rho^2=2) : residueRoot p rho hr^2=2 := by
  let r : ℤ_[p] := ⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩
  have he : r^2=2 := by apply Subtype.ext; exact hr
  have hh := congrArg (PadicInt.toZMod (p:=p)) he
  simpa only [map_pow,map_ofNat] using hh

lemma residue_coefficient (rho : ℚ_[p]) (hr : rho^2=2) :
    PadicInt.toZMod (coefficient p rho hr)=(3-residueRoot p rho hr)^2 := by
  let r : ℤ_[p] := ⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩
  have he : coefficient p rho hr=(3-r)^2 := by
    apply Subtype.ext
    exact ActualSplitOrbitEntry318.coefficient_eq p rho hr
  have hh := congrArg (PadicInt.toZMod (p:=p)) he
  simpa only [map_pow,map_sub,map_ofNat] using hh

/-- The finite residue equation is exactly the original normalized model
with the same selected sqrt2, not an unrelated curve having a known count. -/
@[expose] def pointCount (rho : ℚ_[p]) (hr : rho^2=2) : ℕ :=
  1+Nat.card {z : ZMod p × ZMod p // z.2^2=z.1^3-(3-residueRoot p rho hr)^2*z.1}

theorem actual_quotient_card (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2) (h7 : ¬p∣49) :
    Nat.card ((E (embedding p rho hr ConcreteG8Domain.D)).Point ⧸
      SelectedQuotientOrders318.subgroup p rho hr)=pointCount p rho hr := by
  have he := GoodReductionCardinality318.cardinality p hp (coefficient p rho hr)
    (coefficient_unit p rho hr h7)
  change Nat.card ((E (embedding p rho hr ConcreteG8Domain.D)).Point ⧸
    SelectedQuotientOrders318.subgroup p rho hr)=
      1+Nat.card (ResidueCurve p (coefficient p rho hr)) at he
  simpa only [pointCount,ResidueCurve,residue_coefficient] using he

/-- A genuine divisibility comparison for the SAME half-point quotient
order and the literal full finite-curve count. The stronger count/4 CM
comparison still requires the original doubling-image calculation. -/
theorem actual_order_dvd (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2) (h7 : ¬p∣49) :
    SelectedQuotientOrders318.order p rho hr∣pointCount p rho hr := by
  rw [←actual_quotient_card p rho hr hp h7]
  exact addOrderOf_dvd_natCard (SelectedQuotientOrders318.generator p rho hr)

open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318

@[expose] def counts {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ)
    (hv : Values C u w) (r : Roots C u w hv) (opposite : Bool) (i : Fin 3 × Fin 5) : ℕ :=
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  if opposite then pointCount p (-(r i).val) (negative_root p (r i).val (r i).property)
  else pointCount p (r i).val (r i).property

/-- The actual two LCM moduli divide LCMs of the literal finite-curve
counts, simultaneously at every original position and chosen orientation.
This is a concrete comparison; dividing those counts by4 is not inferred. -/
theorem actual_moduli_dvd_counts {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ)
    (hv : Values C u w) (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5, 49<(row C u w i.1 i.2).natAbs) :
    minus C u w hv r∣Finset.univ.lcm (counts C u w hv r false) ∧
    plus C u w hv r∣Finset.univ.lcm (counts C u w hv r true) := by
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
    exact (actual_order_dvd p (r i).val (r i).property hp h7).trans
      (show counts C u w hv r false i∣Finset.univ.lcm (counts C u w hv r false) from
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
    exact (actual_order_dvd p (-(r i).val) (negative_root p (r i).val (r i).property) hp h7).trans
      (show counts C u w hv r true i∣Finset.univ.lcm (counts C u w hv r true) from
        Finset.dvd_lcm (Finset.mem_univ i))

end SelectedReductionOrder318
