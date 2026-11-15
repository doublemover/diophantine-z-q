module
public import ContactRootReciprocals318
public import ContactBranchDifferential318
public section
noncomputable section
namespace BranchOriginalCoordinate318
open ContactKummerOrder318 ContactRootReciprocals318 SourceFiniteBranch318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Tensor
variable {R A B C D:Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
lemma first_root (a:A):
    (Algebra.TensorProduct.assoc R R R A B (C⊗[R]D)) ((a⊗ₜ[R](1:B))⊗ₜ[R](1:C⊗[R]D))=
      a⊗ₜ[R](1:B⊗[R](C⊗[R]D)):=by
  rw [Algebra.TensorProduct.assoc_tmul,←Algebra.TensorProduct.one_def]
lemma second_root (b:B):
    (Algebra.TensorProduct.assoc R R R B A (C⊗[R]D))
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.comm R A B)
        (AlgEquiv.refl:C⊗[R]D≃ₐ[R]C⊗[R]D) ((1:A)⊗ₜ[R]b⊗ₜ[R](1:C⊗[R]D)))=
      b⊗ₜ[R](1:A⊗[R](C⊗[R]D)):=by
  rw [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  change (Algebra.TensorProduct.assoc R R R B A (C⊗[R]D))
    ((Algebra.TensorProduct.comm R A B ((1:A)⊗ₜ[R]b))⊗ₜ[R](1:C⊗[R]D))=_
  rw [Algebra.TensorProduct.comm_tmul]
  exact first_root b
lemma third_root (c:C):
    (Algebra.TensorProduct.assoc R R R C D (A⊗[R]B))
      (Algebra.TensorProduct.comm R (A⊗[R]B) (C⊗[R]D)
        ((1:A⊗[R]B)⊗ₜ[R](c⊗ₜ[R](1:D))))=c⊗ₜ[R](1:D⊗[R](A⊗[R]B)):=by
  rw [Algebra.TensorProduct.comm_tmul]
  exact first_root c
lemma fourth_root (d:D):
    (Algebra.TensorProduct.assoc R R R D C (A⊗[R]B))
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.comm R C D)
        (AlgEquiv.refl:A⊗[R]B≃ₐ[R]A⊗[R]B)
        (Algebra.TensorProduct.comm R (A⊗[R]B) (C⊗[R]D)
          ((1:A⊗[R]B)⊗ₜ[R]((1:C)⊗ₜ[R]d))))=d⊗ₜ[R](1:C⊗[R](A⊗[R]B)):=by
  rw [Algebra.TensorProduct.comm_tmul]
  exact second_root d
end Tensor
variable (c:Fin 4→ℚˣ)
local instance regroupedCommRing (i:Fin 4):CommRing (RegroupedOrder c i):=inferInstance
local instance regroupedAlgebra (i:Fin 4):Algebra (BranchBase c i) (RegroupedOrder c i):=inferInstance
lemma regroup_root (i:Fin 4):sourceRegroup c i (root c i)=
    algebraMap (BranchBase c i) (RegroupedOrder c i) (ContactFrameNormalization318.branchCoordinate c i):=by
  rw [ContactBranchCoordinate318.branchCoordinate_eq_root]
  fin_cases i
  · exact first_root _
  · exact second_root _
  · exact third_root _
  · exact fourth_root _
/-- The normalized branch frame coordinate is literally the original
root with its original sign, on the entire actual localization. -/
theorem coordinate_eq_root (i:Fin 4):ContactFrameNormalization318.sourceCoordinate c i=
    algebraMap (SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i) (root c i):=by
  apply (SourceBranchLocalization318.sourceLocalizationEquiv c i).injective
  rw [ContactFrameNormalization318.sourceCoordinate,AlgEquiv.apply_symm_apply,
    SourceBranchLocalization318.sourceLocalizationEquiv_on_source]
  change ContactFrameNormalization318.branchOrderCoordinate c i=
    localizedSourceEquiv c i (Algebra.TensorProduct.includeRight (sourceRegroup c i (root c i)))
  rw [regroup_root]
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply (BranchBase c i) (OpenBase c i)
    (OpenBase c i⊗[BranchBase c i]RegroupedOrder c i),AlgEquiv.commutes]
  rfl
end BranchOriginalCoordinate318
