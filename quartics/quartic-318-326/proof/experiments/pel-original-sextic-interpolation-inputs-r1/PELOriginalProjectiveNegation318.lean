module
public import PELOriginalNegationConeAlgebra318
public import PELOriginalReducedProjectiveCandidate318
public import ReducedSchemePointFactorization318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public section
noncomputable section
namespace PELOriginalProjectiveNegation318
open AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal
open PELOriginalCubicRelationIdeal318 PELOriginalNegationRelations318
open PELOriginalReducedProjectiveCandidate318
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal degree-preserving coordinate permutation on ambient Proj. -/
@[expose] def gradedNegation : degrees →+*ᵍ degrees where
  __ := polynomialNegation.toRingEquiv.toRingHom
  map_mem {i} {p} hp := polynomialNegation_homogeneous p i hp

lemma gradedNegation_twice : gradedNegation.comp gradedNegation = .id degrees := by
  apply GradedRingHom.ext
  intro p
  exact polynomialNegation_involutive p

lemma irrelevant_le : degrees₊ ≤ degrees₊.map gradedNegation := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi p hp
  have hm : gradedNegation p ∈ degrees₊ :=
    mem_irrelevant_of_mem _ hi (Graded.map_mem _ hp)
  have h := Ideal.mem_map_of_mem gradedNegation.toRingHom hm
  change polynomialNegation (polynomialNegation p) ∈ (degrees₊.map gradedNegation).toIdeal at h
  rwa [polynomialNegation_involutive] at h

@[expose] def ambientNegation : ambient ⟶ ambient := Proj.map gradedNegation irrelevant_le
lemma ambientNegation_twice : ambientNegation ≫ ambientNegation = 𝟙 ambient := by
  unfold ambientNegation
  rw [←Proj.map_comp]
  simp only [gradedNegation_twice,Proj.map_id]
@[expose] def ambientIso : ambient ≅ ambient where
  hom := ambientNegation
  inv := ambientNegation
  hom_inv_id := ambientNegation_twice
  inv_hom_id := ambientNegation_twice
instance : IsIso ambientNegation := (inferInstance : IsIso ambientIso.hom)

variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- The original reduced candidate is preserved at EVERY homogeneous
prime, not just at complex-valued points or on the analytic image. -/
lemma candidate_range : Set.range (inclusion τ hτ ≫ ambientNegation) ⊆ zeroSet τ hτ := by
  rintro p ⟨q,rfl⟩
  apply (ProjectiveSpectrum.mem_zeroLocus degrees _ (relations τ hτ : Set Equations)).mpr
  intro F hF
  change polynomialNegation F ∈ (inclusion τ hτ q).asHomogeneousIdeal
  exact (point_mem_iff τ hτ _).mp ⟨q,rfl⟩ _ (relation_negation τ hτ F hF)

/-- A genuine morphism of the SAME original reduced candidate scheme,
obtained from its actual radical ideal-sheaf universal factorization. -/
@[expose] def candidateNegation : candidate τ hτ ⟶ candidate τ hτ :=
  ReducedSchemePointFactorization318.factor (inclusion τ hτ ≫ ambientNegation)
    (zeroSet τ hτ) (candidate_range τ hτ)

@[reassoc] lemma candidateNegation_inclusion :
    candidateNegation τ hτ ≫ inclusion τ hτ = inclusion τ hτ ≫ ambientNegation :=
  ReducedSchemePointFactorization318.factor_inclusion _ _ _

lemma candidateNegation_twice : candidateNegation τ hτ ≫ candidateNegation τ hτ =
    𝟙 (candidate τ hτ) := by
  apply (cancel_mono (inclusion τ hτ)).mp
  simp only [Category.assoc,candidateNegation_inclusion,
    candidateNegation_inclusion_assoc,ambientNegation_twice,Category.comp_id,Category.id_comp]

/-- Actual algebraic involution of the entire original projective
candidate. No binary group law or abelian-variety conclusion is inferred. -/
@[expose] def candidateIso : candidate τ hτ ≅ candidate τ hτ where
  hom := candidateNegation τ hτ
  inv := candidateNegation τ hτ
  hom_inv_id := candidateNegation_twice τ hτ
  inv_hom_id := candidateNegation_twice τ hτ
end PELOriginalProjectiveNegation318
