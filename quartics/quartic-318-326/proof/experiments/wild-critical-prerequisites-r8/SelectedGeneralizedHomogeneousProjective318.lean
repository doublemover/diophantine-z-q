module
public import SelectedGeneralizedProjectiveOverlap318
public import ProjectiveAtlas318
public import Mathlib.Tactic.LinearCombination
public section
noncomputable section
open MvPolynomial Algebra AlgebraicGeometry
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SelectedGeneralizedHomogeneousProjective318

variable {R : Type*} [CommRing R]
local notation "P" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R

/-- Literal homogeneous equation of the same generalized model on
the standard projective plane, with all coefficients integral. -/
@[expose] def homogeneousEquation (d : Rˣ) : P :=
  X 1^2*X 2+X 0*X 1*X 2-X 0^3+C (36*(↑d⁻¹ : R))*X 0*X 2^2+
    C (↑d⁻¹ : R)*X 2^3

theorem same_equation (d : Rˣ) :
    homogeneousEquation d = (SelectedGeneralizedJCurve318.curve d).toProjective.polynomial := by
  simp only [homogeneousEquation,SelectedGeneralizedJCurve318.curve,
    WeierstrassCurve.Projective.polynomial,map_one,map_zero,map_neg,map_mul,map_ofNat,zero_mul,one_mul,add_zero]
  ring

theorem isHomogeneous (d : Rˣ) : homogeneousEquation d ∈ G 3 := by
  have h₁ := ((isHomogeneous_X R (1:Fin 3)).pow 2).mul (isHomogeneous_X R 2)
  have h₂ := ((isHomogeneous_X R (0:Fin 3)).mul (isHomogeneous_X R 1)).mul
    (isHomogeneous_X R 2)
  have h₃ := (isHomogeneous_X R (0:Fin 3)).pow 3
  have h₄ := ((isHomogeneous_C (Fin 3) (36*(↑d⁻¹ : R))).mul (isHomogeneous_X R 0)).mul
    ((isHomogeneous_X R 2).pow 2)
  have h₅ := (isHomogeneous_C (Fin 3) (↑d⁻¹ : R)).mul ((isHomogeneous_X R 2).pow 3)
  exact (((h₁.add h₂).sub h₃).add h₄).add h₅

@[expose] def dehomogenize (i : Fin 3) : P →ₐ[R] MvPolynomial (Fin 2) R :=
  (renameEquiv R (finSuccAboveEquiv i).symm).toAlgHom.comp
    (ProjectiveChart318.dehomogenize R (Fin 3) i)

theorem chart_Z (d : Rˣ) : dehomogenize 2 (homogeneousEquation d) = finiteEquation d := by
  simp [dehomogenize,homogeneousEquation,ProjectiveChart318.dehomogenize,finiteEquation] <;> rfl

theorem chart_Y (d : Rˣ) : dehomogenize 1 (homogeneousEquation d) = equation d := by
  simp [dehomogenize,homogeneousEquation,ProjectiveChart318.dehomogenize,equation] <;> rfl

/-- No underlying point of the literal homogeneous hypersurface misses
both true charts. This proof works over arbitrary coefficient rings. -/
theorem actual_support_cover (d : Rˣ) (p : ProjectivePlane318.scheme R)
    (hp : homogeneousEquation d ∈ p.asHomogeneousIdeal) :
    p ∈ Proj.basicOpen G (X 2) ∨ p ∈ Proj.basicOpen G (X 1) := by
  by_contra h
  have hz : X (2:Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hn
    exact h (Or.inl hn)
  have hy : X (1:Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hn
    exact h (Or.inr hn)
  have hxpow : X (0:Fin 3)^3 ∈ p.asHomogeneousIdeal.toIdeal := by
    have hh := p.asHomogeneousIdeal.toIdeal.sub_mem
      (p.asHomogeneousIdeal.toIdeal.mul_mem_left
        (X 1^2+X 0*X 1+C (36*(↑d⁻¹ : R))*X 0*X 2+
          C (↑d⁻¹ : R)*X 2^2) hz) hp
    convert hh using 1
    simp only [homogeneousEquation]
    ring
  have hx : X (0:Fin 3) ∈ p.asHomogeneousIdeal := p.isPrime.mem_of_pow_mem 3 hxpow
  have ht : p ∈ (⊤ : (ProjectivePlane318.scheme R).Opens) := trivial
  rw [← ProjectiveAtlas318.standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at ht
  obtain ⟨i,hi⟩ := ht
  fin_cases i
  · exact hi hx
  · exact hi hy
  · exact hi hz

end SelectedGeneralizedHomogeneousProjective318

#print axioms SelectedGeneralizedHomogeneousProjective318.same_equation
#print axioms SelectedGeneralizedHomogeneousProjective318.chart_Z
#print axioms SelectedGeneralizedHomogeneousProjective318.chart_Y
#print axioms SelectedGeneralizedHomogeneousProjective318.actual_support_cover
