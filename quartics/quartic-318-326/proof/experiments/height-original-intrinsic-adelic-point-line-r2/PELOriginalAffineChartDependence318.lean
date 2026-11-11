module
public import PELOriginalChartFractionDependence318
public import PELOriginalChartSectionField318
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public section
noncomputable section
namespace PELOriginalAffineChartDependence318
open PELOriginalGradedSectionRing318 PELOriginalCubicRelationIdeal318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalChartSectionField318 HomogeneousQuotientChart318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
/-- Every triple of elements of the ACTUAL entire affine coordinate
ring is algebraically dependent over its original complex scalars.
All chart normal forms, nonzero denominators, and the faithful embedding
are produced internally; no selected-subring or supplied normal form
premise is left here. -/
theorem no_independent_triple(z:Fin 3→CoordinateChart τ hτ j):
    ¬AlgebraicIndependent ℂ z:=by
  intro hind
  choose n p hp he using (fun i:Fin 3=>degreeZero_normal_form (relations τ hτ) j (z i))
  have hrep(i:Fin 3):z i=(quotientMap (relations τ hτ) j).rangeRestrict
      (fraction j (n i) (p i) (hp i)):=by
    apply Subtype.ext
    exact (he i).trans (fraction_value (relations τ hτ) j (n i) (p i) (hp i)).symm
  let F:Ring τ hτ→ₐ[ℂ]SectionField τ hτ:=
    IsScalarTower.toAlgHom ℂ (Ring τ hτ) (SectionField τ hτ)
  have hj:F (generators τ hτ j)≠0:=by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j
  have hfun:(algebraEmbedding τ hτ j) ∘ z=
      (fun i=>F (presentation τ hτ (p i))/(F (generators τ hτ j))^(n i)):=by
    funext i
    change embedding τ hτ j (z i)=_
    rw [hrep i,fraction_image]
    rfl
  have hm:=hind.map' (f:=algebraEmbedding τ hτ j) (embedding_injective τ hτ j)
  rw [hfun] at hm
  exact PELOriginalChartFractionDependence318.not_algebraicIndependent τ hτ F j hj n p hp hm
/-- The resulting relation is an ACTUAL polynomial relation in the
whole original affine chart ring, not merely one in a larger field. -/
theorem polynomial_relation(z:Fin 3→CoordinateChart τ hτ j):
    ∃p:MvPolynomial (Fin 3) ℂ,p≠0∧MvPolynomial.aeval z p=0:=by
  have h:=no_independent_triple τ hτ j z
  rw [algebraicIndependent_iff] at h
  push_neg at h
  obtain ⟨p,hp,hne⟩:=h
  exact ⟨p,hne,hp⟩
end PELOriginalAffineChartDependence318
