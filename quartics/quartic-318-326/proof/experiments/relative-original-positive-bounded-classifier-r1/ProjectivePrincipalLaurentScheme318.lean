module
public import ProjectivePrincipalLaurentAlgebra318
public section
noncomputable section
namespace ProjectivePrincipalLaurentScheme318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i : Fin F.size)

/-- The genuine affine-scheme Laurent trivialization of the ORIGINAL
principal coordinate open, not a bijection of points. -/
@[expose] def iso : Spec (CommRingCat.of (H i)) ≅
    Spec (CommRingCat.of (LaurentPolynomial (B i))) :=
  Scheme.Spec.mapIso
    (ProjectivePrincipalLaurentAlgebra318.algebraEquiv R P i).symm.toRingEquiv.toCommRingCatIso.op

@[expose] def projection : Spec (CommRingCat.of (LaurentPolynomial (B i))) ⟶
    ProjectiveParameterSliceSchemes318.chart R P i :=
  Spec.map (CommRingCat.ofHom (algebraMap (B i) (LaurentPolynomial (B i))))

/-- The actual normalization is exactly the coefficient projection of
this literal Laurent algebra, followed by the existing slice inclusion. -/
lemma normalization : (iso R P i).hom ≫ projection R P i ≫
    ProjectiveParameterSliceGluing318.into R P i=
    ProjectiveParameterPrincipalNormalization318.map R P i := by
  have hc := ProjectivePrincipalLaurentAlgebra318.coefficient R P i
  have hn := ProjectivePrincipalTrivializationNatural318.normalization_second R P i
    (CommRingCat.of (H i)) (CommRingCat.of (H i)) (AlgHom.id R (H i))
  have hi : Spec.map (CommRingCat.ofHom (AlgHom.id R (H i)).toRingHom)=
      𝟙 (Spec (CommRingCat.of (H i))) := Spec.map_id _
  rw [hi,Category.id_comp] at hn
  rw [hn]
  rw [←Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom
      (ProjectivePrincipalLaurentAlgebra318.algebraEquiv R P i).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (B i) (LaurentPolynomial (B i))))=_
  rw [←Spec.map_comp]
  exact congrArg (fun a : B i →ₐ[R] H i => Spec.map (CommRingCat.ofHom a.toRingHom)) hc
end ProjectivePrincipalLaurentScheme318
