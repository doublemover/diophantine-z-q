module
public import NormalizedLegendreNativeNegation318
public section
noncomputable section
namespace PELOriginalResidualBranchPoints318
open AlgebraicGeometry CategoryTheory
open PELOriginalOrderedCharacterCoordinate318 PELOriginalDescendedCharacterKernel318
open PELOriginalWholeNativeNegation318
open NormalizedLegendreFieldPoints318 NormalizedLegendreWholeProjection318
open NormalizedLegendreFiniteProjection318
open scoped OnePoint

/-- Actual ORIGINAL residual map, not merely a model sign with the same
character kernel, acts by the exact old completed Legendre coordinates. -/
lemma residual_point_action (i:Fin 4) (p:Option (FinitePoints (parameter i))):
    (schemeEquiv (parameter i) p).val≫(residual i).hom=
      (schemeEquiv (parameter i) (deck (parameter i) p)).val:=by
  rw [residual_eq_native]
  exact NormalizedLegendreNativeNegation318.native_point_action (parameter i) p

/-- Fixed points of the ORIGINAL residual scheme automorphism are exactly
the four correctly ordered branch values, including true infinity. -/
theorem residual_fixed_iff_branch (i:Fin 4) (p:Option (FinitePoints (parameter i))):
    (schemeEquiv (parameter i) p).val≫(residual i).hom=
      (schemeEquiv (parameter i) p).val ↔
    coordinate (parameter i) p=∞ ∨ coordinate (parameter i) p=(0:ℂ) ∨
      coordinate (parameter i) p=(1:ℂ) ∨ coordinate (parameter i) p=(parameter i:ℂ):=by
  rw [residual_point_action]
  have h: (schemeEquiv (parameter i) (deck (parameter i) p)).val=
      (schemeEquiv (parameter i) p).val ↔ deck (parameter i) p=p:=by
    constructor
    · intro h
      exact (schemeEquiv (parameter i)).injective (Subtype.ext h)
    · intro h
      rw [h]
  exact h.trans (fixed_iff_branch (parameter i) p)

/-- All actual completed scheme-valued point fibers are orbits of the
SAME original residual involution; no comparison of mere cardinalities. -/
theorem actual_projection_fiber (i:Fin 4)
    (p q:CompletedFieldPoints318.SchemePoints (K:=ℂ)
      (NormalizedLegendreProjectiveModel318.A (parameter i))
      (NormalizedLegendreProjectiveModel318.B (parameter i))):
    project (parameter i) p=project (parameter i) q ↔
      p=q ∨ p.val≫(residual i).hom=q.val:=by
  obtain ⟨x,rfl⟩:=(schemeEquiv (parameter i)).surjective p
  obtain ⟨y,rfl⟩:=(schemeEquiv (parameter i)).surjective q
  rw [same_projected_scheme_point,residual_point_action]
  constructor
  · rintro (h|h)
    · exact Or.inl (congrArg (schemeEquiv (parameter i)) h)
    · exact Or.inr (congrArg (fun p=>(schemeEquiv (parameter i) p).val) h)
  · rintro (h|h)
    · exact Or.inl ((schemeEquiv (parameter i)).injective h)
    · exact Or.inr ((schemeEquiv (parameter i)).injective (Subtype.ext h))
end PELOriginalResidualBranchPoints318
