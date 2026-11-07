module
public import GlobalGeneratorClosure318
public import GlobalTorsionOddIndex318
public import ActualCanonicalHeight318
public import ActualGlobalRank318
public section
namespace ActualGlobalGenerator318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalSaturationHeight318
open GlobalNormCoset318 CompressedGeneratorBridge318 CircuitReplay Raw318FinalReplay
open RawOddAnchorPoints318 WeierstrassCurve.Affine ActualCanonicalHeight318
set_option maxHeartbeats 0
noncomputable section

/-- All arithmetic, finite enumeration and height inputs are now proved.
No arithmetic, height, group or local-norm premise remains. -/
theorem source_global_labels (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    ∃(labels:Fin 4→ℤ)(c n:ℤ)(τ:E.Point),
      RootLabels w labels ∧ ScalarLabel w c ∧ (∀i,Odd (labels i)) ∧
      (c=labels 1-1 ∨ c= -labels 1-1) ∧ (2*3^32767:ℤ)∣c ∧
      (2:ℝ)^49151<(c.natAbs:ℝ) ∧ n≠0 ∧ (τ=0 ∨ τ=T 0) ∧
      transport curve_eq (CompressedTranslation318.H ((3:ℚ)^65536) w source)=n • P+τ ∧
      transport curve_eq (CompressedTranslation318.V ((3:ℚ)^65536) w source)=(n-1) • P+τ :=
  GlobalGeneratorClosure318.source_global_labels w source canonical_data ActualGlobalRank318.odd_rank_one_data

theorem torsion_is_two_torsion (Q:E.Point) (hq:IsOfFinAddOrder Q) : Q+Q=0 :=
  GlobalTorsionOddIndex318.torsion_is_two_torsion canonical_data Q hq

#print axioms source_global_labels
#print axioms torsion_is_two_torsion
end
end ActualGlobalGenerator318
