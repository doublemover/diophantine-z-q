module
public import RawAnchorNorm318
public import GeneratorMultiplesTwo318
public section
namespace RawOddAnchorPoints318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain AnchorNorm318
open LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Actual point-label interpretation, without any local valuation or parity
hypothesis. It is intentionally separate from the still-open global rank and
raw root reconstruction arguments. -/
@[expose] def RootLabels (w : Assignment) (labels : Fin 4 → ℤ) : Prop :=
  ∀i,∃ (y : K) (h : E.Nonsingular ((RawAnchorNorm318.root w i)^2) y),
    labels i • P=Point.some _ y h

@[expose] def ScalarLabel (w : Assignment) (c : ℤ) : Prop :=
  ∃ (y : K) (h : E.Nonsingular ((RawAnchorNorm318.scalarRoot w)^2) y),
    c • P=Point.some _ y h

theorem root_labels_nonzero (w : Assignment) (labels : Fin 4 → ℤ)
    (hlabels : RootLabels w labels) : ∀i,labels i≠0 := by
  intro i hi
  obtain ⟨y,h,hpt⟩ := hlabels i
  rw [hi,zero_zsmul] at hpt
  exact (Point.some_ne_zero h) hpt.symm

theorem scalar_label_nonzero (w : Assignment) (c : ℤ) (hlabel : ScalarLabel w c) : c≠0 := by
  intro hc
  obtain ⟨y,h,hpt⟩ := hlabel
  rw [hc,zero_zsmul] at hpt
  exact (Point.some_ne_zero h) hpt.symm

theorem root_two_values (w : Assignment) (labels : Fin 4 → ℤ)
    (hlabels : RootLabels w labels) :
    ∀i,padicValRat 2 (norm ((RawAnchorNorm318.root w i)^2))=
      -6-4*(padicValInt 2 (labels i):ℤ) := by
  intro i
  obtain ⟨y,h,hpt⟩ := hlabels i
  exact GeneratorMultiplesTwo318.identified_multiple_norm (labels i)
    (root_labels_nonzero w labels hlabels i) _ y h hpt

theorem scalar_two_value (w : Assignment) (c : ℤ) (hlabel : ScalarLabel w c) :
    padicValRat 2 (norm ((RawAnchorNorm318.scalarRoot w)^2))=
      -6-4*(padicValInt 2 c:ℤ) := by
  have hc := scalar_label_nonzero w c hlabel
  obtain ⟨y,h,hpt⟩ := hlabel
  exact GeneratorMultiplesTwo318.identified_multiple_norm c hc _ y h hpt

/-- The literal source's affine conic now forces every root label odd using
only actual elliptic point interpretation. No 2-adic formula, integral-base
summand, semilocal assertion, or oddness certificate is assumed. -/
theorem source_odd_labels (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels : Fin 4 → ℤ) (c : ℤ)
    (hlabels : RootLabels w labels) (hscalar : ScalarLabel w c) :
    ∀i,Odd (labels i) := by
  have hR := RawAnchorNorm318.scalar_inverse_norm _ w source
  apply RawAnchor318.source_odd_labels_from_norm_values w source labels
    (root_labels_nonzero w labels hlabels) c hR.2.2
  · exact RawAnchorNorm318.scalar_two_value _ w source c _ rfl
      (scalar_two_value w c hscalar)
  · exact RawAnchorNorm318.product_two_value _ w source labels _ (fun _ => rfl)
      (root_two_values w labels hlabels)

/-- With genuine point labels, only the 3-adic local behavior remains in the
anchor-to-index bridge. All 2-adic and source-product premises are discharged. -/
theorem source_anchor_from_points_and_three_values (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels : Fin 4 → ℤ) (c : ℤ)
    (hlabels : RootLabels w labels) (hscalar : ScalarLabel w c)
    (horient : c=labels 1-1 ∨ c= -labels 1-1)
    (hroot3 : ∀i,Odd (labels i) →
      padicValRat 3 (norm ((RawAnchorNorm318.root w i)^2))=0)
    (hscalar3 : Even c → padicValRat 3 (norm ((RawAnchorNorm318.scalarRoot w)^2))=
      -4-4*(padicValInt 3 c:ℤ)) :
    (∀i,Odd (labels i)) ∧ (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) :=
  RawAnchorNorm318.source_anchor_from_individual_point_data w source labels
    (root_labels_nonzero w labels hlabels) c (scalar_label_nonzero w c hscalar)
    horient (root_two_values w labels hlabels) (scalar_two_value w c hscalar) hroot3 hscalar3

end RawOddAnchorPoints318
