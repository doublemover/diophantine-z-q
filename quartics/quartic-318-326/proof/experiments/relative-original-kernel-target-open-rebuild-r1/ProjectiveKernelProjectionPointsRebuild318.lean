module
public import ProjectiveKernelNormalizationAmbient318
public section
noncomputable section
namespace ProjectiveKernelProjectionPointsRebuild318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i : Fin F.size)
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i
local notation "q" => ProjectiveKernelNormalizationAmbient318.coefficient R P Q d i
lemma slice_value (S : Type) [CommRing S] [Algebra R S] (a : D →ₐ[R] S) :
    (ProjectiveKernelNormalizedAlgebras318.points R P Q d i S a).2 = a.comp q := by
  rw [ProjectiveKernelNormalizationAmbient318.coefficient_value]
  simpa only [AlgHom.comp_id] using
    ProjectiveKernelNormalizedAlgebras318.slice_natural R P Q d i D a (AlgHom.id R D)
lemma projection_eq : ProjectiveKernelNormalizedLaurent318.projection R P Q d i =
    Spec.map (CommRingCat.ofHom q.toRingHom) := by
  change (Spec.map (CommRingCat.ofHom
      (ProjectiveKernelNormalizedLaurent318.algebraEquiv R P Q d i).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap C (LaurentPolynomial C)))) = _
  rw [←Spec.map_comp] <;> rfl
/-- The ACTUAL native projection has exactly the normalized algebra
point; no merely abstract equivalence of two coordinate functors. -/
@[reassoc] lemma projection_points (S : CommRingCat.{0}) [Algebra R S] (a : D →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      ProjectiveKernelNormalizedLaurent318.projection R P Q d i =
    Spec.map (CommRingCat.ofHom
      (ProjectiveKernelNormalizedAlgebras318.points R P Q d i S a).2.toRingHom) := by
  rw [projection_eq,←Spec.map_comp,slice_value] <;> rfl
end ProjectiveKernelProjectionPointsRebuild318
