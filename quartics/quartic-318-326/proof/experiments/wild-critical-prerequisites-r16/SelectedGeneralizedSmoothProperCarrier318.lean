module
public import SelectedGeneralizedProjectiveProper318
public import SelectedGeneralizedInfinityCartier318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Algebra
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
open SelectedGeneralizedLocalizedOverlap318 SelectedGeneralizedGluedCarrier318
open SelectedGeneralizedAffineJacobianCover318 SelectedGeneralizedInfinityCartier318

namespace SelectedGeneralizedSmoothProperCarrier318

universe u

variable {R : Type u} [CommRing R]

@[expose] def finitePresentation (d : Rˣ) (i : Fin 2) :
    PreSubmersivePresentation R (FiniteChart d) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := finiteEquations d) (fun _ => i)
    (fun _ _ _ => Subsingleton.elim _ _)

theorem derivative_X (d : Rˣ) : pderiv 0 (finiteEquation d) =
    X 1-3*X 0^2+C (36*(↑d⁻¹ : R)) := by
  simp [finiteEquation] <;> ring

theorem derivative_Y (d : Rˣ) : pderiv 1 (finiteEquation d) = 2*X 1+X 0 := by
  simp [finiteEquation] <;> ring

private theorem finite_jacobian_quotient (d : Rˣ) (i : Fin 2) :
    (finitePresentation d i).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range (finiteEquations d)))
        (pderiv i (finiteEquation d)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

theorem jacobian_X (d : Rˣ) : (finitePresentation d 0).jacobian = gradientX d := by
  rw [finite_jacobian_quotient,derivative_X]
  let q : MvPolynomial (Fin 2) R →+* FiniteChart d :=
    Ideal.Quotient.mk (Ideal.span (Set.range (finiteEquations d)))
  change q (X 1-3*X 0^2+C (36*(↑d⁻¹ : R))) =
    q (X 1)-3*q (X 0)^2+q (C (36*(↑d⁻¹ : R)))
  simp only [map_sub,map_add,map_mul,map_pow,map_ofNat]

theorem jacobian_Y (d : Rˣ) : (finitePresentation d 1).jacobian = gradientY d := by
  rw [finite_jacobian_quotient,derivative_Y]
  simp only [map_add,map_mul,map_ofNat] <;> rfl

theorem finite_smooth (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Algebra.Smooth R (FiniteChart d) := by
  rw [← RingHom.smooth_algebraMap]
  apply RingHom.Smooth.ofLocalizationSpanTarget _ {gradientX d,gradientY d}
    (gradients_span J d hd hJ)
  rintro ⟨r,hr⟩
  rcases Set.mem_insert_iff.mp hr with rfl|hr
  · rw [← IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    have hs : Algebra.Smooth R (Localization.Away (finitePresentation d 0).jacobian) := by
      have := JacobianLocalSmooth318.localization_jacobian (finitePresentation d 0)
      infer_instance
    exact Eq.mp (congrArg (fun f : FiniteChart d => Algebra.Smooth R (Localization.Away f))
      (jacobian_X d)) hs
  · have he : r=gradientY d := Set.mem_singleton_iff.mp hr
    subst r
    rw [← IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    have hs : Algebra.Smooth R (Localization.Away (finitePresentation d 1).jacobian) := by
      have := JacobianLocalSmooth318.localization_jacobian (finitePresentation d 1)
      infer_instance
    exact Eq.mp (congrArg (fun f : FiniteChart d => Algebra.Smooth R (Localization.Away f))
      (jacobian_Y d)) hs

private theorem infinity_jacobian_quotient (d : Rˣ) :
    (presentation d).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range (equations d))) (pderiv 1 (equation d)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

theorem jacobian_Z (d : Rˣ) : (presentation d).jacobian =
    1+parameter d+algebraMap R (Chart d) (72*(↑d⁻¹ : R))*parameter d*ordinate d+
      algebraMap R (Chart d) (3*(↑d⁻¹ : R))*(ordinate d)^2 := by
  rw [infinity_jacobian_quotient,partial_ordinate]
  simp only [map_add,map_mul,map_one,map_pow] <;> rfl

/-- Infinity is either on the known reciprocal affine overlap or
on the smooth Jacobian open, even in the wild characteristics. -/
theorem infinity_cover (d : Rˣ) :
    Ideal.span ({ordinate d,(presentation d).jacobian} : Set (Chart d)) = ⊤ := by
  let I : Ideal (Chart d) := Ideal.span {ordinate d,(presentation d).jacobian}
  apply I.eq_top_iff_one.2
  have hz : ordinate d ∈ I := Ideal.subset_span (by simp)
  have hj : (presentation d).jacobian ∈ I := Ideal.subset_span (by simp)
  let t := parameter d
  let z := ordinate d
  let a := algebraMap R (Chart d) (72*(↑d⁻¹ : R))
  let b := algebraMap R (Chart d) (3*(↑d⁻¹ : R))
  have h := I.sub_mem (I.mul_mem_left (1-t+t^2) hj)
    (I.mul_mem_left ((1-t+t^2)*(a*t+b*z)+factor d) hz)
  have he :
      (1-t+t^2)*(presentation d).jacobian -
        ((1-t+t^2)*(a*t+b*z)+factor d)*z = 1 := by
    rw [jacobian_Z]
    calc
      _ = 1+t^3- z*factor d := by dsimp only [t,z,a,b]; ring
      _ = _ := by rw [show z*factor d=t^3 from equation_factored d]; ring
  exact he ▸ h

theorem infinity_smooth (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Algebra.Smooth R (Chart d) := by
  have hF := finite_smooth J d hd hJ
  have hUZ : Algebra.Smooth R (UZ d) := Algebra.Smooth.comp R (FiniteChart d) _
  have hUY : Algebra.Smooth R (UY d) := Algebra.Smooth.of_equiv (overlap d).symm
  rw [← RingHom.smooth_algebraMap]
  apply RingHom.Smooth.ofLocalizationSpanTarget _ {ordinate d,(presentation d).jacobian}
    (infinity_cover d)
  rintro ⟨r,hr⟩
  rcases Set.mem_insert_iff.mp hr with rfl|hr
  · rw [← IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    exact hUY
  · have he : r=(presentation d).jacobian := Set.mem_singleton_iff.mp hr
    subst r
    rw [← IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    exact SelectedGeneralizedAffineInfinity318.smooth d

theorem finite_structure_smooth (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Smooth (Spec.algebraMap R (FiniteChart d)) :=
  HasRingHomProperty.Spec_iff.2 (RingHom.smooth_algebraMap.2 (finite_smooth J d hd hJ))

theorem infinity_structure_smooth (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Smooth (Spec.algebraMap R (Chart d)) :=
  HasRingHomProperty.Spec_iff.2 (RingHom.smooth_algebraMap.2 (infinity_smooth J d hd hJ))

/-- Whole actual glued carrier smooth (and independently proper), not
only a formal ellipse or a short model valid away from 6. -/
theorem overBase_smooth (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Smooth (overBase d) := by
  letI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Smooth.{u}) (Q := @RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) (f := overBase d)
    (Scheme.IsLocallyDirected.openCover (span (intoZ d) (intoY d))) ?_
  intro i
  cases i with
  | none =>
    change Smooth (colimit.ι (span (intoZ d) (intoY d)) WalkingSpan.zero ≫ overBase d)
    rw [← colimit.w (span (intoZ d) (intoY d)) WalkingSpan.Hom.fst]
    change Smooth (intoZ d ≫ jZ d ≫ overBase d)
    rw [jZ_over]
    have := finite_structure_smooth J d hd hJ
    infer_instance
  | some k =>
    cases k
    · change Smooth (jZ d ≫ overBase d)
      rw [jZ_over]
      exact finite_structure_smooth J d hd hJ
    · change Smooth (jY d ≫ overBase d)
      rw [jY_over]
      exact infinity_structure_smooth J d hd hJ

theorem overBase_smooth_proper (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Smooth (overBase d) ∧ IsProper (overBase d) :=
  ⟨overBase_smooth J d hd hJ,SelectedGeneralizedProjectiveProper318.overBase_proper d⟩

end SelectedGeneralizedSmoothProperCarrier318

#print axioms SelectedGeneralizedSmoothProperCarrier318.overBase_smooth_proper
