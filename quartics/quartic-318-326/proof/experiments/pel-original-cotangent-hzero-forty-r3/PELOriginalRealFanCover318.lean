module
public import PELOriginalVertexDerivatives318
public section
noncomputable section
namespace PELOriginalRealFanCover318
open PELDirichletVertexCycles318 PELDirichletVertexFan318
open PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000
@[expose] def realCross (P Q : ℝ × ℝ) : ℝ := P.1*Q.2-P.2*Q.1
/-- Closed sector between consecutive ACTUAL pulled-back tangent rays.
The reversed orientation of class three is kept explicitly. -/
@[expose] def sector (v : Fin 28) (W : ℝ × ℝ) : Prop :=
  0 ≤ (orientation (vertexClass v):ℝ)*realCross (realPoint (ray v)) W ∧
  0 ≤ (orientation (vertexClass v):ℝ)*realCross W (realPoint (ray (nextVertex v)))

theorem class_0_covers (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v = 0 ∧ sector v W := by
  classical
  by_contra h
  have h0 : ¬ sector 0 W := fun hs => h ⟨0, rfl, hs⟩
  have h1 : ¬ sector 1 W := fun hs => h ⟨1, rfl, hs⟩
  have h12 : ¬ sector 12 W := fun hs => h ⟨12, rfl, hs⟩
  have h13 : ¬ sector 13 W := fun hs => h ⟨13, rfl, hs⟩
  have h14 : ¬ sector 14 W := fun hs => h ⟨14, rfl, hs⟩
  have h15 : ¬ sector 15 W := fun hs => h ⟨15, rfl, hs⟩
  have h26 : ¬ sector 26 W := fun hs => h ⟨26, rfl, hs⟩
  have h27 : ¬ sector 27 W := fun hs => h ⟨27, rfl, hs⟩
  simp only [sector, not_and_or, not_le] at h0 h1 h12 h13 h14 h15 h26 h27
  norm_num [realCross, realPoint, ray, nextVertex, vertexClass, orientation] at h0 h1 h12 h13 h14 h15 h26 h27
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h12 with h12 | h12 <;> rcases h13 with h13 | h13 <;> rcases h14 with h14 | h14 <;> rcases h15 with h15 | h15 <;> rcases h26 with h26 | h26 <;> rcases h27 with h27 | h27 <;> linarith

theorem class_1_covers (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v = 1 ∧ sector v W := by
  classical
  by_contra h
  have h2 : ¬ sector 2 W := fun hs => h ⟨2, rfl, hs⟩
  have h3 : ¬ sector 3 W := fun hs => h ⟨3, rfl, hs⟩
  have h10 : ¬ sector 10 W := fun hs => h ⟨10, rfl, hs⟩
  have h11 : ¬ sector 11 W := fun hs => h ⟨11, rfl, hs⟩
  have h16 : ¬ sector 16 W := fun hs => h ⟨16, rfl, hs⟩
  have h17 : ¬ sector 17 W := fun hs => h ⟨17, rfl, hs⟩
  have h24 : ¬ sector 24 W := fun hs => h ⟨24, rfl, hs⟩
  have h25 : ¬ sector 25 W := fun hs => h ⟨25, rfl, hs⟩
  simp only [sector, not_and_or, not_le] at h2 h3 h10 h11 h16 h17 h24 h25
  norm_num [realCross, realPoint, ray, nextVertex, vertexClass, orientation] at h2 h3 h10 h11 h16 h17 h24 h25
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rcases h10 with h10 | h10 <;> rcases h11 with h11 | h11 <;> rcases h16 with h16 | h16 <;> rcases h17 with h17 | h17 <;> rcases h24 with h24 | h24 <;> rcases h25 with h25 | h25 <;> linarith

theorem class_2_covers (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v = 2 ∧ sector v W := by
  classical
  by_contra h
  have h4 : ¬ sector 4 W := fun hs => h ⟨4, rfl, hs⟩
  have h5 : ¬ sector 5 W := fun hs => h ⟨5, rfl, hs⟩
  have h22 : ¬ sector 22 W := fun hs => h ⟨22, rfl, hs⟩
  have h23 : ¬ sector 23 W := fun hs => h ⟨23, rfl, hs⟩
  simp only [sector, not_and_or, not_le] at h4 h5 h22 h23
  norm_num [realCross, realPoint, ray, nextVertex, vertexClass, orientation] at h4 h5 h22 h23
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;> rcases h22 with h22 | h22 <;> rcases h23 with h23 | h23 <;> linarith

theorem class_3_covers (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v = 3 ∧ sector v W := by
  classical
  by_contra h
  have h6 : ¬ sector 6 W := fun hs => h ⟨6, rfl, hs⟩
  have h7 : ¬ sector 7 W := fun hs => h ⟨7, rfl, hs⟩
  have h20 : ¬ sector 20 W := fun hs => h ⟨20, rfl, hs⟩
  have h21 : ¬ sector 21 W := fun hs => h ⟨21, rfl, hs⟩
  simp only [sector, not_and_or, not_le] at h6 h7 h20 h21
  norm_num [realCross, realPoint, ray, nextVertex, vertexClass, orientation] at h6 h7 h20 h21
  rcases h6 with h6 | h6 <;> rcases h7 with h7 | h7 <;> rcases h20 with h20 | h20 <;> rcases h21 with h21 | h21 <;> linarith

theorem class_4_covers (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v = 4 ∧ sector v W := by
  classical
  by_contra h
  have h8 : ¬ sector 8 W := fun hs => h ⟨8, rfl, hs⟩
  have h9 : ¬ sector 9 W := fun hs => h ⟨9, rfl, hs⟩
  have h18 : ¬ sector 18 W := fun hs => h ⟨18, rfl, hs⟩
  have h19 : ¬ sector 19 W := fun hs => h ⟨19, rfl, hs⟩
  simp only [sector, not_and_or, not_le] at h8 h9 h18 h19
  norm_num [realCross, realPoint, ray, nextVertex, vertexClass, orientation] at h8 h9 h18 h19
  rcases h8 with h8 | h8 <;> rcases h9 with h9 | h9 <;> rcases h18 with h18 | h18 <;> rcases h19 with h19 | h19 <;> linarith

/-- Every real direction is covered, in each of the FIVE original vertex
cycles. This is stronger than the signed-axis-count certificate, but is
not yet a local quotient-disk theorem. -/
theorem every_real_direction (i : Fin 5) (W : ℝ × ℝ) :
    ∃ v : Fin 28, vertexClass v=i ∧ sector v W := by
  fin_cases i
  · exact class_0_covers W
  · exact class_1_covers W
  · exact class_2_covers W
  · exact class_3_covers W
  · exact class_4_covers W
end PELOriginalRealFanCover318
