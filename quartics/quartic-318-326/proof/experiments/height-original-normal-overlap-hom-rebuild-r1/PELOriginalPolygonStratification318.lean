module
public import PELOriginalPolygonBoundary318
public import PELOriginalInteriorUniqueness318
public section
noncomputable section
namespace PELOriginalPolygonStratification318
open PELOriginalPolygonBoundary318 PELStrictPolygonExtension318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318
open PELOriginalDirichletPolygon318 PELOriginalProjectiveTangents318
open PELRealKleinSideTransport318
set_option maxHeartbeats 1800000

/-- Every weak polygon point is either strict or on one of the28 literal
closed sides. Repeated signed axis rows are retained and explicitly mapped. -/
theorem strict_or_closed_side (P : ℝ × ℝ) (hP : P∈planePolygon) :
    strictInequalities P.1 P.2 ∨
      ∃ (e : Fin 28) (s : ℝ), 0≤s ∧ s≤1 ∧
        P=realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s := by
  classical
  by_cases hs : strictInequalities P.1 P.2
  · exact Or.inl hs
  · right
    change ¬ (∀ (j : Fin 8) (ε δ : Bool),
      (rowFirst j:ℝ)*((sign ε:ℝ)*P.1)+(rowSecond j:ℝ)*((sign δ:ℝ)*P.2)<(rowConstant j:ℝ)) at hs
    push_neg at hs
    obtain ⟨j,ε,δ,hrow⟩ := hs
    have he : realSideValue (signedSide j ε δ) P=0 := by
      rw [signed_row_identity]
      have hw := hP j ε δ
      linarith
    obtain ⟨s,hs0,hs1,hline⟩ := whole_boundary_side (signedSide j ε δ) P hP he
    exact ⟨signedSide j ε δ,s,hs0,hs1,hline⟩

/-- Complete real-point stratification: genuine strict interior, a literal
vertex, or a point strictly between the endpoints of a literal side. -/
theorem actual_plane_stratification (P : ℝ × ℝ) (hP : P∈planePolygon) :
    strictInequalities P.1 P.2 ∨
      (∃ v : Fin 28, P=realPoint (vertex v)) ∨
      ∃ (e : Fin 28) (s : ℝ), 0<s ∧ s<1 ∧
        P=realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s := by
  rcases strict_or_closed_side P hP with hs | ⟨e,s,hs0,hs1,hline⟩
  · exact Or.inl hs
  · right
    by_cases hz : s=0
    · left
      exact ⟨start e,by simpa [hz,realMix] using hline⟩
    · by_cases ho : s=1
      · left
        exact ⟨finish e,by simpa [ho,realMix] using hline⟩
      · right
        exact ⟨e,s,lt_of_le_of_ne hs0 (Ne.symm hz),lt_of_le_of_ne hs1 ho,hline⟩
end PELOriginalPolygonStratification318
