module
public import PELOriginalNegationRelations318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace PELOriginalNegationConeAlgebra318
open PELOriginalCubicRelationIdeal318 PELOriginalNegationRelations318
open PELOriginalLevelTheta318 AlgebraicGeometry CategoryTheory
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma relations_map : relations τ hτ =
    (relations τ hτ).map polynomialNegation.toRingEquiv.toRingHom := by
  apply le_antisymm
  · intro p hp
    have h := Ideal.mem_map_of_mem polynomialNegation.toRingEquiv.toRingHom
      (relation_negation τ hτ p hp)
    change polynomialNegation (polynomialNegation p) ∈
      (relations τ hτ).map polynomialNegation.toRingEquiv.toRingHom at h
    rwa [polynomialNegation_involutive] at h
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    exact relation_negation τ hτ p hp

/-- Actual algebraic inversion of the whole homogeneous coordinate cone.
This acts on the original relation quotient, not a transported point set. -/
@[expose] def coneNegation : (Equations ⧸ relations τ hτ) ≃ₐ[ℂ]
    (Equations ⧸ relations τ hτ) :=
  Ideal.quotientEquivAlg (relations τ hτ) (relations τ hτ)
    polynomialNegation (relations_map τ hτ)

lemma coneNegation_mk (p : Equations) :
    coneNegation τ hτ (Ideal.Quotient.mk (relations τ hτ) p) =
      Ideal.Quotient.mk (relations τ hτ) (polynomialNegation p) := rfl

lemma coneNegation_variable (r : Label 3) :
    coneNegation τ hτ (Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X r)) =
      Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X (-r)) := by
  rw [coneNegation_mk]
  rfl

lemma coneNegation_involutive : Function.Involutive (coneNegation τ hτ) := by
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [coneNegation_mk,coneNegation_mk,polynomialNegation_involutive]

/-- A genuine affine SCHEME automorphism of the actual homogeneous cone.
Projective descent and a binary candidate multiplication are separate. -/
@[expose] def coneSchemeNegation :
    Spec (CommRingCat.of (Equations ⧸ relations τ hτ)) ≅
      Spec (CommRingCat.of (Equations ⧸ relations τ hτ)) :=
  Scheme.Spec.mapIso (coneNegation τ hτ).toRingEquiv.toCommRingCatIso.op
end PELOriginalNegationConeAlgebra318
