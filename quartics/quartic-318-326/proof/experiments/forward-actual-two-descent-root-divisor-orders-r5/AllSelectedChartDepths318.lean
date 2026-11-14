module
public import SelectedQuotientOrders318
public section
noncomputable section
namespace AllSelectedChartDepths318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ValuativeOrbitBounds318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- The remaining Gaussian/reduction-order input is now a divisibility
statement about the actual finite formal quotient of the original half-point.
No coordinate depth or positive reciprocal branch is included as a premise. -/
@[expose] def OrderData (u w : ℤ) (hp : Values C u w) (Mminus Mplus : ℕ) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    3≤p ∧ ∃ (rho : ℚ_[p]) (hr : rho^2=2),
      SelectedQuotientOrders318.order p rho hr∣Mminus ∧
      SelectedQuotientOrders318.order p (-rho) (ConcretePadic318.negative_root p rho hr)∣Mplus

/-- Every actual selected contact receives the same finalh. The primary
Pi³ exponent produces u-depth4 and delta-depth16; the opposite residue1
produces u-depth1 and delta-depth4, for EVERY signed multiplier n. This is
not yet the Padé comparison-depth theorem for the twelve squared leaves. -/
theorem actual_depths (u w : ℤ) (hp : Values C u w) (Mminus Mplus h : ℕ)
    (horders : OrderData C u w hp Mminus Mplus)
    (hprimary : Nat.ModEq ((product C u w)^3*Mminus) h 0)
    (hopposite : Nat.ModEq Mplus h 1) :
    ∀ j : Fin 3, ∀ i : Fin 5,
      let p := (row C u w j i).natAbs
      letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
      ∃ (rho : ℚ_[p]) (hr : rho^2=2), ∀ n : ℤ,
        Bound (ConcretePadic318.place p rho hr) 4 (CoherentMultipleCharts318.chartU (n*(h:ℤ))) ∧
        Bound (ConcretePadic318.place p rho hr) 16 (CoherentMultipleCharts318.chartV (n*(h:ℤ))-1) ∧
        Bound (ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hr)) 1
          (CoherentMultipleCharts318.chartU (n*((h:ℤ)-1))) ∧
        Bound (ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hr)) 4
          (CoherentMultipleCharts318.chartV (n*((h:ℤ)-1))-1) := by
  intro j i
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  obtain ⟨hp3,rho,hr,hm,hp'⟩ := horders j i
  refine ⟨rho,hr,?_⟩
  intro n
  exact SelectedPositiveDelta318.original_charts p hp3 rho hr (product C u w) Mminus Mplus h
    (selected_divides C u w (j,i))
    (SelectedQuotientOrders318.entry_of_order_dvd p rho hr Mminus hm)
    (SelectedQuotientOrders318.entry_of_order_dvd p (-rho) _ Mplus hp')
    hprimary hopposite n

end AllSelectedChartDepths318
