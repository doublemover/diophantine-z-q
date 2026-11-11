module
public import ProjectivePrincipalTrivializationNatural318
public import LaurentUnitPoints318
public import AlgebraPointEquivalence318
public section
noncomputable section
namespace ProjectivePrincipalLaurentAlgebra318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i : Fin F.size)

@[expose] def points (S : Type) [CommRing S] [Algebra R S] :
    (H i →ₐ[R] S) ≃ (LaurentPolynomial (B i) →ₐ[R] S) :=
  (ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of S)).trans
    (LaurentUnitPoints318.points R (B i) S).symm

lemma natural (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (g : S →ₐ[R] T) (a : H i →ₐ[R] S) :
    points R P i T (g.comp a)=g.comp (points R P i S a) := by
  apply (LaurentUnitPoints318.points R (B i) T).injective
  have h (U : Type) [CommRing U] [Algebra R U] (b : H i →ₐ[R] U) :
      LaurentUnitPoints318.points R (B i) U (points R P i U b)=
      ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of U) b :=
    (LaurentUnitPoints318.points R (B i) U).apply_symm_apply _
  apply Prod.ext
  · rw [h,LaurentUnitPoints318.unit_natural,h]
    exact ProjectivePrincipalTrivializationNatural318.unit_natural R P i
      (CommRingCat.of S) (CommRingCat.of T) g a
  · rw [h,LaurentUnitPoints318.coefficient_natural,h]
    exact ProjectivePrincipalTrivializationNatural318.slice_natural R P i
      (CommRingCat.of S) (CommRingCat.of T) g a

/-- The ORIGINAL principal section algebra is actually the Laurent algebra
of the ORIGINAL normalized slice. Both inverse maps are recovered from
natural all-ring points, not just residue-field points. -/
@[expose] def algebraEquiv : H i ≃ₐ[R] LaurentPolynomial (B i) :=
  AlgebraPointEquivalence318.algebraEquiv R (H i) (LaurentPolynomial (B i))
    (points R P i) (natural R P i)

lemma evaluation (S : Type) [CommRing S] [Algebra R S] (a : H i →ₐ[R] S) :
    points R P i S a=a.comp (algebraEquiv R P i).symm.toAlgHom :=
  AlgebraPointEquivalence318.evaluate R (H i) (LaurentPolynomial (B i))
    (points R P i) (natural R P i) S a

/-- The actual inverse Laurent map carries its coefficient subalgebra to
exactly the normalized slice map of the original principal chart. -/
lemma coefficient : (algebraEquiv R P i).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (B i) (LaurentPolynomial (B i)))=
    (ProjectivePrincipalUnitTrivialization318.trivialization R P i
      (CommRingCat.of (H i)) (AlgHom.id R (H i))).2 := by
  have he := evaluation R P i (H i) (AlgHom.id R (H i))
  rw [AlgHom.id_comp] at he
  have h := (LaurentUnitPoints318.points R (B i) (H i)).apply_symm_apply
    (ProjectivePrincipalUnitTrivialization318.trivialization R P i
      (CommRingCat.of (H i)) (AlgHom.id R (H i)))
  change LaurentUnitPoints318.points R (B i) (H i)
    (points R P i (H i) (AlgHom.id R (H i)))=_ at h
  rw [he] at h
  exact congrArg Prod.snd h
end ProjectivePrincipalLaurentAlgebra318
