module
public import ActualRawProductHeight318
public import ActualGlobalGenerator318
public section
noncomputable section
namespace SourceMaxIndexHeight318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 GlobalSaturationHeight318 RawProductHeight318
set_option maxHeartbeats 0

/-- The literal source constraints alone yield actual odd integer root
labels and the exact maximum-index product-height lower bound. -/
theorem source_max_index_data (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    ∃(labels:Fin 4→ℤ)(c:ℤ),
      RootLabels w labels ∧ ScalarLabel w c ∧ (∀i,Odd (labels i)) ∧
      (c=labels 1-1 ∨ c= -labels 1-1) ∧
      (2:ℝ)^49151<(c.natAbs:ℝ) ∧
      (c.natAbs:ℝ)≤(maxIndex labels:ℝ)+1 ∧
      3≤(maxIndex labels:ℝ) ∧
      NumberField.absLogHeight₁ ((Kprod w)^2)=∑i,xHeight ((labels i) • P) ∧
      (maxIndex labels:ℝ)^2-6<NumberField.absLogHeight₁ ((Kprod w)^2) := by
  obtain ⟨labels,c,n,τ,hlabels,hscalar,hodd,horient,_,hlarge,_⟩ :=
    ActualGlobalGenerator318.source_global_labels w source
  have hc : 4<(c.natAbs:ℝ) := by
    have hh : (4:ℝ)≤2^49151 := by
      calc
        (4:ℝ)=2^2 := by norm_num
        _≤2^49151 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact hh.trans_lt hlarge
  exact ⟨labels,c,hlabels,hscalar,hodd,horient,hlarge,
    scalar_abs_le_maxIndex_add_one labels c horient,
    three_le_maxIndex_of_scalar_bound labels c horient hc,
    ActualRawProductHeight318.source_height_identity _ w source labels hlabels hodd,
    ActualRawProductHeight318.source_max_index_lower _ w source labels hlabels hodd⟩

#print axioms source_max_index_data
end SourceMaxIndexHeight318
