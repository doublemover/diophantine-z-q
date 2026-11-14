module
public import JLineAtlas318
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace OriginalProjectiveBaseIntegral318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reducedness is checked on the actual two polynomial charts of the
original projective line, not supplied by a geometric PEL hypothesis. -/
theorem reduced : IsReduced (ProjectiveJLine318.scheme ℚ) := by
  let C : (ProjectiveJLine318.scheme ℚ).OpenCover := {
    I₀ := Fin 2
    X := fun _ => Spec (CommRingCat.of (Polynomial ℚ))
    f := JLineAtlas318.chart ℚ
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, inferInstance⟩
      intro x
      have hx : x ∈ (⊤ : (ProjectiveJLine318.scheme ℚ).Opens) := trivial
      rw [← JLineAtlas318.standard_opens_cover ℚ, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨j, hj⟩ := hx
      rw [← JLineAtlas318.chart_range] at hj
      obtain ⟨q, hq⟩ := hj
      exact ⟨j, q, hq⟩ }
  letI : ∀ i : C.I₀, IsReduced (C.X i) :=
    fun _ => inferInstanceAs (IsReduced (Spec (CommRingCat.of (Polynomial ℚ))))
  exact IsReduced.of_openCover (X := ProjectiveJLine318.scheme ℚ) C


/-- The actual integral dominant quotient of the original integral curve is
surjective and makes the already reduced projective base integral. -/
theorem integral {Y : Scheme} [IsIntegral Y]
    (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p] [IsIntegralHom p] :
    IsIntegral (ProjectiveJLine318.scheme ℚ) := by
  letI : Surjective p :=
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  letI : IrreducibleSpace (ProjectiveJLine318.scheme ℚ) :=
    p.surjective.irreducibleSpace p.continuous
  letI := reduced
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end OriginalProjectiveBaseIntegral318
