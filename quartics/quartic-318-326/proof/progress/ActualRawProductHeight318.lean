module
public import RawProductHeight318
public import ActualOddProductHeight318
public section
noncomputable section
namespace ActualRawProductHeight318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 GlobalSaturationHeight318 RawProductHeight318
set_option maxHeartbeats 0

/-- The literal squared root product has exactly the sum of the four actual
abscissa heights. Every finite-place input has now been discharged. -/
theorem source_height_identity (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) (hodd:∀i,Odd (labels i)) :
    NumberField.absLogHeight₁ ((Kprod w)^2)=∑i,xHeight ((labels i) • P) := by
  rw [source_squared_product S w source labels hlabels]
  exact ActualOddProductHeight318.odd_multiple_height_product Finset.univ labels (fun i _=>hodd i)

/-- The actual source lower bound with B exactly max_i|n_i| and no
finite-place, abstract-height, or canonical-data premise. -/
theorem source_max_index_lower (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) (hodd:∀i,Odd (labels i)) :
    (maxIndex labels:ℝ)^2-6<NumberField.absLogHeight₁ ((Kprod w)^2) :=
  max_index_lower_of_height_identity w labels (source_height_identity S w source labels hlabels hodd)

/-- At the literal anchor scale, oddness itself follows from the actual
root and scalar point labels and the exact source residuals. -/
theorem anchored_source_max_index_lower (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Fin 4→ℤ) (c:ℤ)
    (hlabels:RootLabels w labels) (hscalar:ScalarLabel w c) :
    (maxIndex labels:ℝ)^2-6<NumberField.absLogHeight₁ ((Kprod w)^2) :=
  source_max_index_lower _ w source labels hlabels
    (source_odd_labels w source labels c hlabels hscalar)

#print axioms source_height_identity
#print axioms source_max_index_lower
#print axioms anchored_source_max_index_lower
end ActualRawProductHeight318
