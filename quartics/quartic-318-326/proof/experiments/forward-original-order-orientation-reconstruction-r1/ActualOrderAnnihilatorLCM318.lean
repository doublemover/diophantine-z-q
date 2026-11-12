module
public import ActualSelectedUniformOrderGrowth318
public section
noncomputable section
namespace ActualOrderAnnihilatorLCM318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
@[expose] def Entries (r : Roots C u w hv) (opposite : Bool) (M : ℕ) : Prop :=
  ∀ i : Fin 3 × Fin 5,
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    if opposite then SelectedFormalEntry318.Entry p (-(r i).val)
      (ConcretePadic318.negative_root p (r i).val (r i).property) M
    else SelectedFormalEntry318.Entry p (r i).val (r i).property M
lemma primary_iff (r : Roots C u w hv) (M : ℕ) :
    Entries C u w hv r false M ↔ minus C u w hv r∣M := by
  constructor
  · intro h
    apply Finset.lcm_dvd
    intro i hi
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    exact (SelectedExactEntryOrders318.entry_iff _ _ _ M).mp (h i)
  · intro h i
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    exact (SelectedExactEntryOrders318.entry_iff _ _ _ M).mpr
      ((primary_dvd C u w hv r i).trans h)
lemma opposite_iff (r : Roots C u w hv) (M : ℕ) :
    Entries C u w hv r true M ↔ plus C u w hv r∣M := by
  constructor
  · intro h
    apply Finset.lcm_dvd
    intro i hi
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    exact (SelectedExactEntryOrders318.entry_iff _ _ _ M).mp (h i)
  · intro h i
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
    exact (SelectedExactEntryOrders318.entry_iff _ _ _ M).mpr
      ((opposite_dvd C u w hv r i).trans h)
end ActualOrderAnnihilatorLCM318
