module
public import SelectedGeneralizedGluedCarrier318
public import SelectedGeneralizedHomogeneousProjective318
public import ProjectiveEvaluation318
public section
noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318
open SelectedGeneralizedLocalizedOverlap318 SelectedGeneralizedGluedCarrier318
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SelectedGeneralizedProjectiveMap318

variable {R : Type*} [CommRing R]
local notation "P" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R

@[expose] def finiteHom (d : Rˣ) : Away G (X 2) →ₐ[R] FiniteChart d :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (finiteEquations d)))).comp
    (ProjectiveAtlas318.chartEquiv R 2).toAlgHom

@[expose] def infinityHom (d : Rˣ) : Away G (X 1) →ₐ[R] Chart d :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (equations d)))).comp
    (ProjectiveAtlas318.chartEquiv R 1).toAlgHom

@[simp] theorem finiteHom_x (d : Rˣ) :
    finiteHom d ((ProjectiveAtlas318.chartEquiv R 2).symm (X 0)) = x d := by
  simp [finiteHom,x]
@[simp] theorem finiteHom_y (d : Rˣ) :
    finiteHom d ((ProjectiveAtlas318.chartEquiv R 2).symm (X 1)) = y d := by
  simp [finiteHom,y]
@[simp] theorem infinityHom_t (d : Rˣ) :
    infinityHom d ((ProjectiveAtlas318.chartEquiv R 1).symm (X 0)) = parameter d := by
  simp [infinityHom,parameter]
@[simp] theorem infinityHom_z (d : Rˣ) :
    infinityHom d ((ProjectiveAtlas318.chartEquiv R 1).symm (X 1)) = ordinate d := by
  simp [infinityHom,ordinate]

@[expose] def overlapCoords (d : Rˣ) : P →ₐ[R] UY d := aeval ![it d,1,iz d]
theorem overlap_Y_unit (d : Rˣ) : IsUnit (overlapCoords d (X 1)) := by simp [overlapCoords]
theorem overlap_Z_unit (d : Rˣ) : IsUnit (overlapCoords d (X 2)) := by
  simp only [overlapCoords,aeval_X,Matrix.cons_val_two]
  exact IsUnit.of_mul_eq_one _ (iz_ii d)

theorem relation_Z (d : Rˣ) : (toUYbase d).comp (finiteHom d) =
    ProjectiveEvaluation318.chartEval (overlapCoords d) 2 (overlap_Z_unit d) := by
  apply ProjectiveAtlas318.chart_hom_ext R 2
  intro i
  have hz : overlapCoords d (X 2)*ii d=1 := by simpa [overlapCoords] using iz_ii d
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ (ii d) hz]
  fin_cases i
  · simp [AlgHom.comp_apply,overlapCoords,toUYbase,
      show (2:Fin 3).succAbove (0:Fin 2)=0 from rfl]
  · simp [AlgHom.comp_apply,overlapCoords,toUYbase,
      show (2:Fin 3).succAbove (1:Fin 2)=1 from rfl]

theorem relation_Y (d : Rˣ) :
    (Algebra.algHom R (Chart d) (UY d)).comp (infinityHom d) =
      ProjectiveEvaluation318.chartEval (overlapCoords d) 1 (overlap_Y_unit d) := by
  apply ProjectiveAtlas318.chart_hom_ext R 1
  intro i
  have hy : overlapCoords d (X 1)*(1:UY d)=1 := by simp [overlapCoords]
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 hy]
  fin_cases i
  · simp [AlgHom.comp_apply,overlapCoords,it] <;> rfl
  · simp [AlgHom.comp_apply,overlapCoords,iz] <;> rfl

@[expose] def finiteMap (d : Rˣ) : Finite d ⟶ ProjectivePlane318.scheme R :=
  Spec.map (CommRingCat.ofHom (finiteHom d).toRingHom) ≫
    Proj.awayι G (X 2) (isHomogeneous_X R 2) (by decide)

@[expose] def infinityMap (d : Rˣ) : Infinity d ⟶ ProjectivePlane318.scheme R :=
  Spec.map (CommRingCat.ofHom (infinityHom d).toRingHom) ≫
    Proj.awayι G (X 1) (isHomogeneous_X R 1) (by decide)

theorem maps_agree (d : Rˣ) : intoZ d ≫ finiteMap d = intoY d ≫ infinityMap d := by
  rw [intoZ_ring]
  unfold finiteMap infinityMap intoY
  rw [← Spec.map_comp_assoc,← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((toUYbase d).comp (finiteHom d)).toRingHom) ≫ _ =
    Spec.map (CommRingCat.ofHom ((Algebra.algHom R (Chart d) (UY d)).comp
      (infinityHom d)).toRingHom) ≫ _
  rw [relation_Z,relation_Y]
  exact ProjectiveEvaluation318.chart_compatibility (overlapCoords d).toRingHom
    (X 2) (X 1) (overlap_Z_unit d) (overlap_Y_unit d)
    (isHomogeneous_X R 2) (isHomogeneous_X R 1) (by decide) (by decide)

/-- Genuine map into the actual projective plane from the same
two-chart generalized scheme carrying the identity and jets. -/
@[expose] def embedding (d : Rˣ) : Carrier d ⟶ ProjectivePlane318.scheme R :=
  pushout.desc (finiteMap d) (infinityMap d) (maps_agree d)

@[simp] theorem finite_embedding (d : Rˣ) : jZ d ≫ embedding d = finiteMap d :=
  pushout.inl_desc ..
@[simp] theorem infinity_embedding (d : Rˣ) : jY d ≫ embedding d = infinityMap d :=
  pushout.inr_desc ..

end SelectedGeneralizedProjectiveMap318

#print axioms SelectedGeneralizedProjectiveMap318.maps_agree
#print axioms SelectedGeneralizedProjectiveMap318.finite_embedding
