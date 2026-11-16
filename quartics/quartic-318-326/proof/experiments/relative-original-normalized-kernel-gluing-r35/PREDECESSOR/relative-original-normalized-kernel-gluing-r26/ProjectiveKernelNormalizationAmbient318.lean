module
public import ProjectiveKernelNormalizedGluing318
public section
noncomputable section
namespace ProjectiveKernelNormalizationAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i : Fin F.size)
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P i
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
local notation "E" => ProjectiveKernelNormalizedLaurent318.algebraEquiv R P Q d i
local notation "qb" => ProjectiveKernelNormalizedAlgebras318.sliceQuotient R P Q d i
local notation "qh" => ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i
local notation "oldPoint" => ProjectivePrincipalUnitTrivialization318.trivialization R P i
local notation "newPoint" => ProjectiveKernelNormalizedAlgebras318.points R P Q d i
@[expose] def coefficient : C i →ₐ[R] D :=
  E.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (C i) (LaurentPolynomial (C i)))
lemma coefficient_value : coefficient R P Q d i=(newPoint D (AlgHom.id R D)).2 := by
  have he := ProjectiveKernelNormalizedLaurent318.evaluation R P Q d i D (AlgHom.id R D)
  rw [AlgHom.id_comp] at he
  have h := (LaurentUnitPoints318.points R (C i) D).apply_symm_apply
    (newPoint D (AlgHom.id R D))
  change LaurentUnitPoints318.points R (C i) D
    (ProjectiveKernelNormalizedLaurent318.points R P Q d i D (AlgHom.id R D))=_ at h
  rw [he] at h
  exact congrArg Prod.snd h
/-- The new normalized coefficient map is literally the OLD ambient
normalization map modulo the full kernel equations. -/
lemma coefficient_quotient : (coefficient R P Q d i).comp qb=
    qh.comp (oldPoint (CommRingCat.of H) (AlgHom.id R H)).2 := by
  rw [coefficient_value,ProjectiveKernelNormalizedAlgebras318.slice_quotient]
  simpa only [AlgHom.id_comp,AlgHom.comp_id] using
    ProjectivePrincipalTrivializationNatural318.slice_natural R P i
      (CommRingCat.of H) (CommRingCat.of D) qh (AlgHom.id R H)
lemma affine_square : ProjectiveKernelNormalizedLaurent318.projection R P Q d i ≫
    ProjectiveKernelOverlapAlgebras318.sliceInto R P Q d i=
      Spec.map (CommRingCat.ofHom qh.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (oldPoint (CommRingCat.of H) (AlgHom.id R H)).2.toRingHom) := by
  change (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (C i) (LaurentPolynomial (C i))))) ≫
      Spec.map (CommRingCat.ofHom qb.toRingHom)=_
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (coefficient_quotient R P Q d i)
/-- Local normalization now lands in the ACTUALLY GLUED kernel scheme. -/
@[expose] def localMap : Spec (CommRingCat.of D) ⟶ ProjectiveKernelNormalizedGluing318.scheme R P Q d :=
  ProjectiveKernelNormalizedLaurent318.projection R P Q d i ≫
    ProjectiveKernelNormalizedGluing318.into R P Q d i
@[reassoc] lemma localMap_ambient : localMap R P Q d i ≫ ProjectiveKernelNormalizedGluing318.closedInto R P Q d=
    Spec.map (CommRingCat.ofHom qh.toRingHom) ≫ ProjectiveParameterPrincipalNormalization318.map R P i := by
  have hn := ProjectivePrincipalTrivializationNatural318.normalization_second R P i
    (CommRingCat.of H) (CommRingCat.of H) (AlgHom.id R H)
  have hi : Spec.map (CommRingCat.ofHom (AlgHom.id R H).toRingHom)=𝟙 (Spec (CommRingCat.of H)) := Spec.map_id _
  rw [hi,Category.id_comp] at hn
  simp only [localMap,Category.assoc,ProjectiveKernelNormalizedGluing318.into_closedInto,
    ProjectiveKernelAmbientIntersection318.ambientMap]
  rw [←Category.assoc,affine_square,Category.assoc,←hn]

end ProjectiveKernelNormalizationAmbient318
