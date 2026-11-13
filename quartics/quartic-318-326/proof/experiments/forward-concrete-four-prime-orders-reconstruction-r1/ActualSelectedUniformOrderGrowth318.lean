module
public import ConcreteGaussianOppositePrimeFactor318
public section
noncomputable section
namespace ActualSelectedUniformOrderGrowth318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- One explicit bound works at ALL original positions and BOTH roots. -/
theorem all_orders (r : Roots C u w hv) (T : ℕ)
    (hlarge : ∀ i : Fin 3 × Fin 5, SelectedUniformOrderGrowth318.bound T<
      (row C u w i.1 i.2).natAbs) :
    ∀ i, T<primaryOrder C u w hv r i ∧ T<oppositeOrder C u w hv r i := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  exact ⟨SelectedUniformOrderGrowth318.large_order p (r i).val (r i).property T (hlarge i),
    SelectedUniformOrderGrowth318.large_order p (-(r i).val)
      (ConcretePadic318.negative_root p (r i).val (r i).property) T (hlarge i)⟩
lemma all_nontrivial (r : Roots C u w hv) :
    ∀ i, 1<primaryOrder C u w hv r i ∧ 1<oppositeOrder C u w hv r i := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  exact ⟨SelectedOriginalGeneratorNonzero318.order_gt_one p _ _,
    SelectedOriginalGeneratorNonzero318.order_gt_one p _ _⟩
end ActualSelectedUniformOrderGrowth318
