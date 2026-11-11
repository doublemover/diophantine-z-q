module
public import FourRootTensorUniversal318
public import ThreeRootCoordinates318
public section
noncomputable section
namespace ThreeRootTensorUniversal318
open scoped TensorProduct
open QuadraticPresentation318 ThreeRootOrder318 ThreeRootCoordinates318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (a:Fin 3→R) (z:Fin 3→S) (hz:∀k,z k^2=algebraMap R S (a k))

lemma generator_square (k:Fin 3):generator a k^2=algebraMap R (Order a) (a k):=by
  fin_cases k <;> simp [generator,Algebra.TensorProduct.tmul_pow,root_square,
    Algebra.TensorProduct.algebraMap_def,←AdjoinRoot.algebraMap_eq,
    FourRootOrderSigns318.scalar_right]
  · exact FourRootOrderSigns318.scalar_right (A:=RootRing (a 0))
      (B:=RootRing (a 1)⊗[R]RootRing (a 2)) (a 1)
  · exact FourRootOrderSigns318.scalar_right (A:=RootRing (a 0))
      (B:=RootRing (a 1)⊗[R]RootRing (a 2)) (a 2)

@[expose] def rootHom (k:Fin 3):RootRing (a k)→ₐ[R]S:=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) (z k) (by
    change Polynomial.aeval (z k) (Polynomial.X^2-Polynomial.C (a k))=0
    simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,hz,sub_self])
@[simp] theorem rootHom_root (k:Fin 3):
    rootHom a z hz k (AdjoinRoot.root (polynomial (a k)))=z k:=
  AdjoinRoot.liftAlgHom_root _ _ _ _
@[expose] def lift:Order a→ₐ[R]S:=
  Algebra.TensorProduct.lift (rootHom a z hz 0)
    (Algebra.TensorProduct.lift (rootHom a z hz 1) (rootHom a z hz 2) (fun _ _=>Commute.all _ _))
    (fun _ _=>Commute.all _ _)
@[simp] theorem lift_generator (k:Fin 3):lift a z hz (generator a k)=z k:=by
  fin_cases k <;> simp [generator,lift,Algebra.TensorProduct.lift_tmul]
end ThreeRootTensorUniversal318
