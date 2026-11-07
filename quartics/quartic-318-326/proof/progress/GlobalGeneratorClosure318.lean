module
public import GlobalSaturation318
public import RawCompressedLabels318
public import GlobalDualSquare318
public import GlobalFirstDescent318
public import PrimitiveQuadraticMahler318
public section
namespace GlobalGeneratorClosure318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalSaturationHeight318
open GlobalNormCoset318 CompressedGeneratorBridge318 CircuitReplay Raw318FinalReplay
open RawOddAnchorPoints318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- One source-specific actual-group interface supplying every root, scalar,
and H/V integer label needed by the local soundness composition. All finite
search, source reconstruction, norm, parity and Kummer work is discharged.
The dual and first-descent field arithmetic are now proved; only the
global rank/odd-index and canonical-height inputs remain. -/
theorem source_global_labels (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    {height:E.Point→ℝ} (d:CanonicalData height)
    (rank:GlobalSaturationLogic318.OddRankOneData)
    :
    ∃(labels:Fin 4→ℤ)(c n:ℤ)(τ:E.Point),
      RootLabels w labels ∧ ScalarLabel w c ∧ (∀i,Odd (labels i)) ∧
      (c=labels 1-1 ∨ c= -labels 1-1) ∧ (2*3^32767:ℤ)∣c ∧
      (2:ℝ)^49151<(c.natAbs:ℝ) ∧ n≠0 ∧ (τ=0 ∨ τ=T 0) ∧
      transport curve_eq (CompressedTranslation318.H ((3:ℚ)^65536) w source)=n • P+τ ∧
      transport curve_eq (CompressedTranslation318.V ((3:ℚ)^65536) w source)=(n-1) • P+τ := by
  have hg := GlobalSaturation318.square_point_generation d PrimitiveQuadraticMahler318.polynomial_height_coverage rank GlobalDualSquare318.dual_square_abscissa
  obtain ⟨labels,c,hl,hc,ho,hor,hdiv,hbound⟩ :=
    RawGroupAnchor318.source_anchor_from_group_generation w source hg
  obtain ⟨n,τ,ht,hH,hV⟩ := RawCompressedLabels318.source_HV_labels _ w source GlobalFirstDescent318.first_descent_classes hg
  have hn := RawCompressedLabels318.source_H_label_ne_zero _ w source n τ ht hH
  exact ⟨labels,c,n,τ,hl,hc,ho,hor,hdiv,hbound,hn,ht,hH,hV⟩

end
end GlobalGeneratorClosure318
