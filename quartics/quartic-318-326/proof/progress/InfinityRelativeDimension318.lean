module
public import AffineRelativeDimension318
public import WeierstrassGluing318
public section
noncomputable section
namespace InfinityRelativeDimension318
open Algebra MvPolynomial InfinityChart318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

@[expose] def twoPresentations (A B : R) (i : Fin 2) :
    PreSubmersivePresentation R (Ring A B) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations A B) (fun _ => i)
    (fun _ _ _ => Subsingleton.elim _ _)

lemma jacobian_formula (A B : R) (i : Fin 2) :
    (twoPresentations A B i).jacobian=Ideal.Quotient.mk _ (pderiv i (equation A B)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

lemma pderiv_x (A B : R) : pderiv 0 (equation A B)= -3*X 0^2-C A*X 1^2 := by
  simp [equation]
  ring

lemma jacobian_x (A B : R) : (twoPresentations A B 0).jacobian=
    -3*x A B^2-algebraMap R (Ring A B) A*z A B^2 := by
  rw [jacobian_formula,pderiv_x]
  simp only [map_sub,map_neg,map_mul,map_pow,map_ofNat]
  rfl

lemma jacobian_z (A B : R) : (twoPresentations A B 1).jacobian=
    1-2*algebraMap R (Ring A B) A*x A B*z A B-3*algebraMap R (Ring A B) B*z A B^2 :=
  InfinityChart318.jacobian_formula A B

/-- The actual Y=1 chart's Jacobian ideal contains 2, independently of the discriminant. -/
theorem two_identity (A B : R) : (2 : Ring A B)=
    (2-(2*algebraMap R (Ring A B) A*x A B+3*algebraMap R (Ring A B) B*z A B)*z A B)*
      (twoPresentations A B 1).jacobian-
    (2*algebraMap R (Ring A B) A*x A B+3*algebraMap R (Ring A B) B*z A B)*x A B*
      (twoPresentations A B 0).jacobian := by
  rw [jacobian_x,jacobian_z]
  linear_combination 3*(2*algebraMap R (Ring A B) A*x A B+3*algebraMap R (Ring A B) B*z A B)*relation A B

lemma jacobian_span (A B : R) (h2 : IsUnit (2:R)) :
    Ideal.span (Set.range (fun i : Fin 2 => (twoPresentations A B i).jacobian))=⊤ := by
  let I := Ideal.span (Set.range (fun i : Fin 2 => (twoPresentations A B i).jacobian))
  apply I.eq_top_of_isUnit_mem (x := 2)
  · rw [two_identity]
    exact I.sub_mem (I.mul_mem_left _ (Ideal.subset_span ⟨1,rfl⟩))
      (I.mul_mem_left _ (Ideal.subset_span ⟨0,rfl⟩))
  · simpa only [map_ofNat] using h2.map (algebraMap R (Ring A B))

open AlgebraicGeometry in
/-- The whole actual infinity chart is smooth of relative dimension one wherever 2 is invertible. -/
theorem structure_dimension_one (A B : R) (h2 : IsUnit (2:R)) :
    SmoothOfRelativeDimension 1 (InfinitySmooth318.structureMap A B) := by
  apply HasRingHomProperty.Spec_iff.mpr
  refine ⟨Set.range (fun i : Fin 2 => (twoPresentations A B i).jacobian),jacobian_span A B h2,?_⟩
  rintro t ⟨i,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap (Ring A B) (Localization.Away (twoPresentations A B i).jacobian)).comp
      (algebraMap R (Ring A B)))
  rw [←IsScalarTower.algebraMap_eq,RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact AffineRelativeDimension318.localization_dimension_one (twoPresentations A B i)

end InfinityRelativeDimension318
