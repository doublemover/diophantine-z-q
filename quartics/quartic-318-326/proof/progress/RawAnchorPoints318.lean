module
public import RawOddAnchorPoints318
public import OddMultiplesThree318
public section
namespace RawAnchorPoints318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open RawOddAnchorPoints318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Full literal anchor conclusion from actual elliptic point labels and
Kummer orientation. Every 2-adic and 3-adic valuation statement is proved by
actual group arithmetic, not retained as a hypothesis. -/
theorem source_anchor_from_points (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels : Fin 4 → ℤ) (c : ℤ)
    (hlabels : RootLabels w labels) (hscalar : ScalarLabel w c)
    (horient : c=labels 1-1 ∨ c= -labels 1-1) :
    (∀i,Odd (labels i)) ∧ (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  apply source_anchor_from_points_and_three_values w source labels c hlabels hscalar horient
  · intro i hi
    obtain ⟨y,h,hpt⟩ := hlabels i
    exact OddMultiplesThree318.identified_odd_multiple_norm (labels i) hi _ y h hpt
  · intro heven
    have hc := scalar_label_nonzero w c hscalar
    obtain ⟨y,h,hpt⟩ := hscalar
    exact GeneratorMultiplesThree318.identified_even_multiple_norm c hc heven _ y h hpt

end RawAnchorPoints318
