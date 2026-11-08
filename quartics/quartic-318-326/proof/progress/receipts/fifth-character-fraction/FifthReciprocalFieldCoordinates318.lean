module
public import FifthReciprocalFraction318
public section
noncomputable section
namespace FifthReciprocalFieldCoordinates318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318 FifthCharacterReciprocal318
open FifthReciprocalCoordinates318 FifthReciprocalFraction318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
@[expose] def t:Field:=FifthCharacterOrder318.embedding (algebraMap R QOrder X)
@[expose] def y:Field:=FifthCharacterOrder318.embedding (AdjoinRoot.root (polynomial quartic))
@[expose] def openEmbedding:QuarticOpen→+*Field:=
  quarticEmbedding.comp quarticBaseChange.symm.toRingHom
lemma openEmbedding_root : openEmbedding (AdjoinRoot.root (polynomial (algebraMap R Laurent quartic)))=y := by
  change quarticEmbedding ((ContactGenericFiber318.rootBaseChange (S:=Laurent) quartic).symm (AdjoinRoot.root _))=y
  rw [←ContactGenericFiber318.rootBaseChange_generator (S:=Laurent) quartic,
    AlgEquiv.symm_apply_apply]
  exact quarticEmbedding_on_order _
lemma openEmbedding_parameter : openEmbedding (algebraMap Laurent QuarticOpen (LaurentPolynomial.T 1))=t := by
  have hb:quarticBaseChange (algebraMap QOrder QuarticTensor (algebraMap R QOrder X))=
      algebraMap Laurent QuarticOpen (LaurentPolynomial.T 1) := by
    rw [←IsScalarTower.algebraMap_apply R QOrder QuarticTensor]
    rw [IsScalarTower.algebraMap_apply R Laurent QuarticTensor,AlgEquiv.commutes]
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
  change quarticEmbedding (quarticBaseChange.symm _)=t
  rw [←hb,AlgEquiv.symm_apply_apply]
  exact quarticEmbedding_on_order _
lemma openEmbedding_inverseParameter :
    openEmbedding (algebraMap Laurent QuarticOpen (LaurentPolynomial.T (-1)))=t⁻¹ := by
  have h:openEmbedding (algebraMap Laurent QuarticOpen (LaurentPolynomial.T (-1)))*t=1 := by
    rw [←openEmbedding_parameter,←map_mul,←map_mul,←LaurentPolynomial.T_add]
    norm_num
  exact eq_inv_of_mul_eq_one_left h
lemma openEmbedding_inverseSquare :
    openEmbedding (algebraMap Laurent QuarticOpen (LaurentPolynomial.T (-2)))=t⁻¹^2 := by
  have h:(LaurentPolynomial.T (-2):Laurent)=LaurentPolynomial.T (-1)^2 := by
    rw [LaurentPolynomial.T_pow];rfl
  rw [h,map_pow,map_pow,openEmbedding_inverseParameter]

lemma embedding_v : embedding (AdjoinRoot.root (polynomial reciprocal))=t⁻¹^2*y := by
  change quarticEmbedding (tensorEquiv.symm (1⊗ₜ[R]AdjoinRoot.root (polynomial reciprocal)))=_
  change openEmbedding (equiv.symm (cubicBaseChange (1⊗ₜ[R]AdjoinRoot.root (polynomial reciprocal))))=_
  rw [cubicBaseChange,ContactGenericFiber318.rootBaseChange_generator,inverse_root,map_mul,
    openEmbedding_inverseSquare,openEmbedding_root]

lemma embedding_u : embedding (algebraMap R COrder X)=t⁻¹ := by
  have hb:cubicBaseChange (algebraMap COrder CubicTensor (algebraMap R COrder X))=
      algebraMap Laurent CubicOpen (LaurentPolynomial.T 1) := by
    rw [←IsScalarTower.algebraMap_apply R COrder CubicTensor]
    rw [IsScalarTower.algebraMap_apply R Laurent CubicTensor,AlgEquiv.commutes]
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
  have he:equiv.symm (algebraMap Laurent CubicOpen (LaurentPolynomial.T 1))=
      algebraMap Laurent QuarticOpen (LaurentPolynomial.T (-1)) := by
    apply equiv.injective
    rw [AlgEquiv.apply_symm_apply,equiv_on_base,LaurentPolynomial.invert_T]
    rfl
  change openEmbedding (equiv.symm (cubicBaseChange (algebraMap COrder CubicTensor (algebraMap R COrder X))))=_
  rw [hb,he,openEmbedding_inverseParameter]

/-- Exact original four-root identity retained in the reciprocal fraction field. -/
theorem original_root : (y:FifthCharacterField318.L)=FifthCharacterField318.root :=
  FifthCharacterOrder318.embedding_root
end FifthReciprocalFieldCoordinates318
