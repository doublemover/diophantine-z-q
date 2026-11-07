module
public import ProjectiveEvaluation318
public import WeierstrassGluing318
import all WeierstrassGluing318
public section
noncomputable section
namespace CubicProjectiveMap318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassOverlap318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]
local notation "P" => MvPolynomial (Fin 3) R
local notation "G" => ProjectivePlane318.grading R

@[expose] def finiteHom (A B : R) : Away G (X 2) →ₐ[R] Affine A B :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (ShortAffineJacobian318.equations A B)))).comp
    (ProjectiveAtlas318.chartEquiv R 2).toAlgHom
@[expose] def infinityHom (A B : R) : Away G (X 1) →ₐ[R] Infinity A B :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (InfinityChart318.equations A B)))).comp
    (ProjectiveAtlas318.chartEquiv R 1).toAlgHom

@[simp] theorem finiteHom_x (A B : R) : finiteHom A B ((ProjectiveAtlas318.chartEquiv R 2).symm (X 0))=
    ShortAffineJacobian318.x A B := by simp [finiteHom,ShortAffineJacobian318.x]
@[simp] theorem finiteHom_y (A B : R) : finiteHom A B ((ProjectiveAtlas318.chartEquiv R 2).symm (X 1))=
    ShortAffineJacobian318.y A B := by simp [finiteHom,ShortAffineJacobian318.y]
@[simp] theorem infinityHom_x (A B : R) : infinityHom A B ((ProjectiveAtlas318.chartEquiv R 1).symm (X 0))=
    InfinityChart318.x A B := by simp [infinityHom,InfinityChart318.x]
@[simp] theorem infinityHom_z (A B : R) : infinityHom A B ((ProjectiveAtlas318.chartEquiv R 1).symm (X 1))=
    InfinityChart318.z A B := by simp [infinityHom,InfinityChart318.z]

@[expose] def overlapCoordinates (A B : R) : P →ₐ[R] InfinityOverlap A B := aeval ![ix A B,1,iz A B]
lemma overlap_Y_unit (A B : R) : IsUnit (overlapCoordinates A B (X 1)) := by simp [overlapCoordinates]
lemma overlap_Z_unit (A B : R) : IsUnit (overlapCoordinates A B (X 2)) := by
  simp only [overlapCoordinates,aeval_X,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero]
  exact IsUnit.of_mul_eq_one _ (iz_ii A B)

lemma finite_overlap (A B : R) : (toInfinityBase A B).comp (finiteHom A B)=
    ProjectiveEvaluation318.chartEval (overlapCoordinates A B) 2 (overlap_Z_unit A B) := by
  apply ProjectiveAtlas318.chart_hom_ext R 2
  intro i
  have hz : overlapCoordinates A B (X 2)*ii A B=1 := by simpa [overlapCoordinates] using iz_ii A B
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ (ii A B) hz]
  fin_cases i
  · simp [AlgHom.comp_apply,overlapCoordinates,show (2:Fin 3).succAbove (0:Fin 2)=0 from rfl,show (2:Fin 3).succAbove (1:Fin 2)=1 from rfl]
  · simp [AlgHom.comp_apply,overlapCoordinates,show (2:Fin 3).succAbove (0:Fin 2)=0 from rfl,show (2:Fin 3).succAbove (1:Fin 2)=1 from rfl]

lemma infinity_overlap (A B : R) : (Algebra.algHom R (Infinity A B) (InfinityOverlap A B)).comp (infinityHom A B)=
    ProjectiveEvaluation318.chartEval (overlapCoordinates A B) 1 (overlap_Y_unit A B) := by
  apply ProjectiveAtlas318.chart_hom_ext R 1
  intro i
  have hy : overlapCoordinates A B (X 1)*(1:InfinityOverlap A B)=1 := by simp [overlapCoordinates]
  rw [ProjectiveEvaluation318.chartEval_X _ _ _ _ 1 hy]
  fin_cases i
  · simp [AlgHom.comp_apply,overlapCoordinates,ix]
    rfl
  · simp [AlgHom.comp_apply,overlapCoordinates,iz]
    rfl

@[expose] def finiteMap (A B : R) : ShortAffineScheme318.scheme A B ⟶ ProjectivePlane318.scheme R :=
  Spec.map (CommRingCat.ofHom (finiteHom A B).toRingHom) ≫
    Proj.awayι G (X 2) (isHomogeneous_X R 2) (by omega)
@[expose] def infinityMap (A B : R) : InfinitySmooth318.scheme A B ⟶ ProjectivePlane318.scheme R :=
  Spec.map (CommRingCat.ofHom (infinityHom A B).toRingHom) ≫
    Proj.awayι G (X 1) (isHomogeneous_X R 1) (by omega)

/-- The two actual cubic chart maps into homogeneous Proj agree on the actual overlap. -/
theorem overlap_compatible (A B : R) :
    WeierstrassGluing318.intoAffine A B ≫ finiteMap A B=
      WeierstrassGluing318.intoInfinity A B ≫ infinityMap A B := by
  rw [WeierstrassGluing318.intoAffine_eq]
  unfold finiteMap infinityMap WeierstrassGluing318.intoInfinity
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((toInfinityBase A B).comp (finiteHom A B)).toRingHom) ≫ _=
    Spec.map (CommRingCat.ofHom ((Algebra.algHom R (Infinity A B) (InfinityOverlap A B)).comp
      (infinityHom A B)).toRingHom) ≫ _
  rw [finite_overlap,infinity_overlap]
  exact ProjectiveEvaluation318.chart_compatibility (overlapCoordinates A B).toRingHom
    (X 2) (X 1) (overlap_Z_unit A B) (overlap_Y_unit A B)
    (isHomogeneous_X R 2) (isHomogeneous_X R 1) (by omega) (by omega)

/-- The actual globally glued cubic morphism to the actual proper projective plane. -/
@[expose] def embedding (A B : R) : WeierstrassGluing318.scheme A B ⟶ ProjectivePlane318.scheme R :=
  pushout.desc (finiteMap A B) (infinityMap A B) (overlap_compatible A B)
@[simp] theorem finite_embedding (A B : R) : WeierstrassGluing318.finiteChart A B ≫ embedding A B=finiteMap A B :=
  pushout.inl_desc ..
@[simp] theorem infinity_embedding (A B : R) : WeierstrassGluing318.infinityChart A B ≫ embedding A B=infinityMap A B :=
  pushout.inr_desc ..

end CubicProjectiveMap318
