module
public import FourRootPivot318
public import FourRootOrderSigns318
public section
noncomputable section
namespace ActualRootPivotCoordinates318
open scoped TensorProduct
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
variable {R:Type*} [CommRing R] (a:Fin 4→R)
lemma regroup_generator (i:Fin 4):
    FourRootPivot318.regroup a i (FourRootOrderSigns318.generator a i)=
      algebraMap (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0)))
        (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0))⊗[R]
          ThreeRootOrder318.Order (fun j=>a (FourRootPivot318.indices i j.succ)))
        (AdjoinRoot.root (QuadraticPresentation318.polynomial (a (FourRootPivot318.indices i 0)))):=by
  fin_cases i
  · exact first_root _
  · exact second_root _
  · exact third_root _
  · exact fourth_root _
end ActualRootPivotCoordinates318
