module
public import FiniteActiveHalfplanes318
public import PELActualOriginalSideGluing318
public section
noncomputable section
namespace PELOriginalLocalCones318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318
open PELOriginalProjectiveTangents318 PELOriginalDirichletPolygon318
open PELActualOriginalSideGluing318
@[expose] def RowIndex := Fin 8 × Bool × Bool
@[expose] def linearRow (i : RowIndex) (W : ℝ × ℝ) : ℝ :=
  (rowFirst i.1:ℝ)*((sign i.2.1:ℝ)*W.1)+
  (rowSecond i.1:ℝ)*((sign i.2.2:ℝ)*W.2)
@[expose] def constantRow (i : RowIndex) : ℝ := rowConstant i.1
/-- Full original active-constraint cone, including repeated signed rows.
No replacement by an abstract fan or by the rational j-map occurs here. -/
@[expose] def vertexCone (v : Fin 28) : Set (ℝ × ℝ) := {W |
  ∀ i : RowIndex, linearRow i (realPoint (vertex v)) = constantRow i → linearRow i W ≤ 0}

theorem linearRow_continuous (i : RowIndex) : Continuous (linearRow i) :=
  (continuous_const.mul (continuous_const.mul continuous_fst)).add
    (continuous_const.mul (continuous_const.mul continuous_snd))

theorem linearRow_sub (i : RowIndex) (P Q : ℝ × ℝ) :
    linearRow i (P-Q)=linearRow i P-linearRow i Q := by
  change (rowFirst i.1:ℝ)*((sign i.2.1:ℝ)*(P.1-Q.1))+
    (rowSecond i.1:ℝ)*((sign i.2.2:ℝ)*(P.2-Q.2))=
    ((rowFirst i.1:ℝ)*((sign i.2.1:ℝ)*P.1)+(rowSecond i.1:ℝ)*((sign i.2.2:ℝ)*P.2))-
    ((rowFirst i.1:ℝ)*((sign i.2.1:ℝ)*Q.1)+(rowSecond i.1:ℝ)*((sign i.2.2:ℝ)*Q.2))
  ring

theorem polygon_iff (P : ℝ × ℝ) : P ∈ planePolygon ↔
    ∀ i : RowIndex, linearRow i P ≤ constantRow i := by
  constructor
  · intro h i
    exact h i.1 i.2.1 i.2.2
  · intro h j ε δ
    exact h (j, ε, δ)

/-- Every literal vertex has an OPEN real-plane neighborhood on which
membership in the SAME actual polygon is EXACTLY its translated full cone.
This is a geometric neighborhood statement, not only a derivative table. -/
theorem actual_vertex_cone_neighborhood (v : Fin 28) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ realPoint (vertex v) ∈ U ∧
      ∀ P ∈ U, P ∈ planePolygon ↔ P-realPoint (vertex v) ∈ vertexCone v := by
  have hp := (polygon_iff _).mp (vertex_in_polygon v)
  obtain ⟨U,hU,hv,hlocal⟩ := FiniteActiveHalfplanes318.local_active_constraints
    linearRow linearRow_continuous constantRow (realPoint (vertex v)) hp
  refine ⟨U,hU,hv,?_⟩
  intro P hP
  rw [polygon_iff, hlocal P hP]
  constructor
  · intro h i hi
    change linearRow i (P-realPoint (vertex v)) ≤ 0
    rw [linearRow_sub, hi]
    exact sub_nonpos.mpr (h i hi)
  · intro h i hi
    have hh := h i hi
    change linearRow i (P-realPoint (vertex v)) ≤ 0 at hh
    rw [linearRow_sub, hi] at hh
    exact sub_nonpos.mp hh
end PELOriginalLocalCones318
