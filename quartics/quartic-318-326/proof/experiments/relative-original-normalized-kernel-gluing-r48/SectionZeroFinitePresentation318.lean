module
public import ProjectiveSectionIdeal318
public import Mathlib.RingTheory.FinitePresentation
public section
noncomputable section
namespace SectionZeroFinitePresentation318
open scoped BigOperators
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P] (s : P)

/-- Explicit finite equations for the original zero ideal, furnished by
its actual projective dual frame. No free basis of P is assumed. -/
lemma ideal_eq_frame_span : ProjectiveSectionIdeal318.ideal R P s =
    Ideal.span (Set.range (fun i => (FiniteProjectiveEvaluationFrame318.frame R P).coordinate i s)) := by
  classical
  let F := FiniteProjectiveEvaluationFrame318.frame R P
  apply le_antisymm
  · rintro a ⟨φ,rfl⟩
    have hs := congrArg φ (F.reconstruct s)
    rw [map_sum] at hs
    rw [← hs]
    apply Ideal.sum_mem
    intro i _
    rw [map_smul,smul_eq_mul]
    apply Ideal.mul_mem_right
    exact Ideal.subset_span ⟨i,rfl⟩
  · apply Ideal.span_le.mpr
    rintro a ⟨i,rfl⟩
    exact ⟨F.coordinate i,rfl⟩

lemma ideal_fg : (ProjectiveSectionIdeal318.ideal R P s).FG := by
  classical
  let F := FiniteProjectiveEvaluationFrame318.frame R P
  refine ⟨Finset.univ.image (fun i => F.coordinate i s),?_⟩
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using
    (ideal_eq_frame_span R P s).symm

/-- The actual affine section zero quotient is finitely presented over
its own chart ring, even over arbitrary non-Noetherian coefficient rings. -/
instance quotient_finitePresentation :
    Algebra.FinitePresentation R (R ⧸ ProjectiveSectionIdeal318.ideal R P s) :=
  Algebra.FinitePresentation.quotient (ideal_fg R P s)
end SectionZeroFinitePresentation318
