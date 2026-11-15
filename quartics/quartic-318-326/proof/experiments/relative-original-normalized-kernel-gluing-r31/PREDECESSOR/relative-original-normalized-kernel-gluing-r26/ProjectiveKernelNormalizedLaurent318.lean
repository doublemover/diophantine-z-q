module
public import ProjectiveKernelNormalizedAlgebras318
public import AlgebraPointEquivalence318
public import LaurentUnitPoints318
public import LaurentProjectionSmooth318
public section
noncomputable section
namespace ProjectiveKernelNormalizedLaurent318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i : Fin F.size)
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i
@[expose] def points (S : Type) [CommRing S] [Algebra R S] :
    (D →ₐ[R] S) ≃ (LaurentPolynomial C →ₐ[R] S) :=
  (ProjectiveKernelNormalizedAlgebras318.points R P Q d i S).trans
    (LaurentUnitPoints318.points R C S).symm
lemma natural (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (g : S →ₐ[R] T) (a : D →ₐ[R] S) :
    points R P Q d i T (g.comp a)=g.comp (points R P Q d i S a) := by
  apply (LaurentUnitPoints318.points R C T).injective
  have h (U : Type) [CommRing U] [Algebra R U] (b : D →ₐ[R] U) :
      LaurentUnitPoints318.points R C U (points R P Q d i U b)=
        ProjectiveKernelNormalizedAlgebras318.points R P Q d i U b :=
    (LaurentUnitPoints318.points R C U).apply_symm_apply _
  apply Prod.ext
  · rw [h,LaurentUnitPoints318.unit_natural,h]
    exact ProjectiveKernelNormalizedAlgebras318.unit_natural R P Q d i S g a
  · rw [h,LaurentUnitPoints318.coefficient_natural,h]
    exact ProjectiveKernelNormalizedAlgebras318.slice_natural R P Q d i S g a
/-- Genuine algebra isomorphism: the principal chart of the actual
linear kernel is the Laurent algebra of its ACTUAL normalized kernel slice. -/
@[expose] def algebraEquiv : D ≃ₐ[R] LaurentPolynomial C :=
  AlgebraPointEquivalence318.algebraEquiv R D (LaurentPolynomial C)
    (points R P Q d i) (natural R P Q d i)
lemma evaluation (S : Type) [CommRing S] [Algebra R S] (a : D →ₐ[R] S) :
    points R P Q d i S a=a.comp (algebraEquiv R P Q d i).symm.toAlgHom :=
  AlgebraPointEquivalence318.evaluate R D (LaurentPolynomial C)
    (points R P Q d i) (natural R P Q d i) S a
@[expose] def schemeIso : Spec (CommRingCat.of D) ≅ Spec (CommRingCat.of (LaurentPolynomial C)) :=
  Scheme.Spec.mapIso (algebraEquiv R P Q d i).symm.toRingEquiv.toCommRingCatIso.op
/-- Concrete normalization map of the SAME kernel principal chart. -/
@[expose] def projection : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of C) :=
  (schemeIso R P Q d i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C (LaurentPolynomial C)))
instance smooth : Smooth (projection R P Q d i) := by
  haveI := LaurentProjectionSmooth318.smooth C
  unfold projection
  infer_instance
instance flat : Flat (projection R P Q d i) := inferInstance
instance presentation : LocallyOfFinitePresentation (projection R P Q d i) := inferInstance
instance affine : IsAffineHom (projection R P Q d i) := by unfold projection;infer_instance

end ProjectiveKernelNormalizedLaurent318
