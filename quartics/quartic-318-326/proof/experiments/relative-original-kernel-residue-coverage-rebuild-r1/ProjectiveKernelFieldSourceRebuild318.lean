module
public import ProjectiveKernelCoordinateDetectionRebuild318
public import ProjectiveKernelNonzeroSourceRebuild318
public section
noncomputable section
namespace ProjectiveKernelFieldSourceRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
variable (K : CommRingCat.{0}) [Field K] [Algebra R K]
  (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] K)
  (ha : ProjectiveKernelParameter318.points R P Q d K a ≠ 0)
local notation "W" => ProjectiveParameterPrincipalCover318.locus R P
local notation "q" => ProjectiveKernelParameter318.quotient R P Q d
/-- Nonzero is used over a FIELD only. It forces the entire Spec K
map into the original ambient nonzero open, not merely a selected point. -/
include ha in
lemma range_nonzero : Set.range (Spec.map (CommRingCat.ofHom (a.comp q).toRingHom)) ⊆
    (W : Set (Spec (CommRingCat.of (ProjectiveSectionParameter318.algebra R P)))) := by
  obtain ⟨i,hi⟩ := (ProjectiveKernelCoordinateDetectionRebuild318.nonzero_iff R P Q d K a).mp ha
  rintro _ ⟨z,rfl⟩
  rw [ProjectiveParameterNonzeroOpen318.mem_locus]
  intro h
  have hx := h (Ideal.subset_span (Set.mem_range_self
    (ProjectiveParameterZeroCoordinates318.coordinate R P i)))
  change a (ProjectiveKernelCoordinateDetectionRebuild318.coordinate R P Q d i) ∈ z.asIdeal at hx
  have ho := z.asIdeal.mul_mem_left
    (a (ProjectiveKernelCoordinateDetectionRebuild318.coordinate R P Q d i))⁻¹ hx
  rw [inv_mul_cancel₀ hi] at ho
  exact z.isPrime.ne_top (Ideal.eq_top_iff_one.mpr ho)
def ambientLift : Spec K ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι (Spec.map (CommRingCat.ofHom (a.comp q).toRingHom)) (by
    rw [Scheme.Opens.range_ι]
    exact range_nonzero R P Q d K a ha)
@[reassoc] lemma ambientLift_fac : ambientLift R P Q d K a ha ≫ W.ι =
    Spec.map (CommRingCat.ofHom (a.comp q).toRingHom) := IsOpenImmersion.lift_fac _ _ _
/-- The point lies in the SAME full-kernel pullback used by global
normalization; no replacement parameter or reduced ideal is substituted. -/
def lift : Spec K ⟶ ProjectiveKernelNonzeroSourceRebuild318.source R P Q d :=
  pullback.lift (Spec.map (CommRingCat.ofHom a.toRingHom)) (ambientLift R P Q d K a ha) (by
    rw [ambientLift_fac, ProjectiveKernelNonzeroSourceRebuild318.ambientInto, ← Spec.map_comp] <;> rfl)
@[reassoc] lemma lift_original : lift R P Q d K a ha ≫
    ProjectiveKernelNonzeroSourceRebuild318.original R P Q d =
      Spec.map (CommRingCat.ofHom a.toRingHom) := pullback.lift_fst _ _ _
end ProjectiveKernelFieldSourceRebuild318
