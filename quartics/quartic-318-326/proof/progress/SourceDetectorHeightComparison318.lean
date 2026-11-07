module
public import ActualDetectorNondegenerate318
public import SourceMaxIndexHeight318
public section
noncomputable section
namespace SourceDetectorHeightComparison318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawProductHeight318 RawWeights318 RawOddAnchorPoints318
set_option maxHeartbeats 0

/-- The literal source alone excludes all five contact roots for each of
its three current rational parameters. The exceptional value t=1 remains allowed. -/
theorem source_contacts_nonzero (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    contactPolynomial (t0 ((3:ℚ)^65536) w)≠0 ∧
      contactPolynomial (t1 ((3:ℚ)^65536) w)≠0 ∧
      contactPolynomial (t2 ((3:ℚ)^65536) w)≠0 := by
  obtain ⟨labels,c,n,τ,hlabels,_⟩ := ActualGlobalGenerator318.source_global_labels w source
  exact ActualDetectorNondegenerate318.source_contacts_nonzero _ w source labels hlabels

/-- The final source-specific numerical comparison, with only the three
actual rational contact-height inequalities left as supplied producers. -/
theorem source_max_index_comparison (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (H:ℝ) (hH:1≤H) (N:ℤ) (hN:N≠0) (k:ℕ)
    (h0:NumberField.absLogHeight₁ (t0 ((3:ℚ)^65536) w)≤
      (H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h1:NumberField.absLogHeight₁ (t1 ((3:ℚ)^65536) w)≤
      (H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h2:NumberField.absLogHeight₁ (t2 ((3:ℚ)^65536) w)≤
      (H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k))) :
    ∃(labels:Fin 4→ℤ)(c:ℤ), RootLabels w labels ∧ ScalarLabel w c ∧
      (∀i,Odd (labels i)) ∧ (c=labels 1-1 ∨ c= -labels 1-1) ∧
      (2:ℝ)^49151<(c.natAbs:ℝ) ∧ (c.natAbs:ℝ)≤(maxIndex labels:ℝ)+1 ∧
      3≤(maxIndex labels:ℝ) ∧
      (maxIndex labels:ℝ)^2-6<7*H*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  obtain ⟨labels,c,hlabels,hscalar,hodd,horient,hlarge,hcB,hB,_,hlower⟩ :=
    SourceMaxIndexHeight318.source_max_index_data w source
  exact ⟨labels,c,hlabels,hscalar,hodd,horient,hlarge,hcB,hB,
    hlower.trans (SourceDetectorScales318.source_height_upper _ w source H hH N hN k h0 h1 h2)⟩

#print axioms source_contacts_nonzero
#print axioms source_max_index_comparison
end SourceDetectorHeightComparison318
