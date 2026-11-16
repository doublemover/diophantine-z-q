module
public import ThreeRootOrder318
public section
noncomputable section
namespace ThreeRootCoordinates318
open scoped TensorProduct
open QuadraticPresentation318 ThreeRootOrder318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] (a:Fin 3→R)
@[expose] def generator:Fin 3→Order a:=
  ![AdjoinRoot.root (polynomial (a 0))⊗ₜ[R]1,
    1⊗ₜ[R](AdjoinRoot.root (polynomial (a 1))⊗ₜ[R]1),
    1⊗ₜ[R](1⊗ₜ[R]AdjoinRoot.root (polynomial (a 2)))]
variable {T:Type*} [CommRing T] [Algebra R T]
theorem hom_ext {f g:Order a→ₐ[R]T}
    (h:∀i,f (generator a i)=g (generator a i)):f=g:=by
  apply Algebra.TensorProduct.ext
  · apply AdjoinRoot.algHom_ext
    exact h 0
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 1
    · apply AdjoinRoot.algHom_ext
      exact h 2
variable (S:Type*) [CommRing S] [Algebra R S]
@[expose] def coefficientMap:Order a→ₐ[R]Order (fun i=>algebraMap R S (a i)):=
  ((baseChange a S).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem coefficientMap_generator (i:Fin 3):
    coefficientMap a S (generator a i)=generator (fun i=>algebraMap R S (a i)) i:=by
  fin_cases i <;>
    simp [coefficientMap,baseChange,FourRootOrder318.pairBaseChange,generator,
      TensorPairBaseChange318.split_one,ContactGenericFiber318.rootBaseChange_generator] <;>
    simp only [←Algebra.TensorProduct.one_def,map_one]
variable {U:Type*} [CommRing U]
/-- Complete ring homomorphism extensionality with the actual coefficient map. -/
theorem ringHom_ext {f g:Order a→+*U}
    (hb:f.comp (algebraMap R (Order a))=g.comp (algebraMap R (Order a)))
    (h:∀i,f (generator a i)=g (generator a i)):f=g:=by
  letI:Algebra R U:=(f.comp (algebraMap R (Order a))).toAlgebra
  let fA:Order a→ₐ[R]U:={f with commutes':=fun _=>rfl}
  let gA:Order a→ₐ[R]U:={g with commutes':=fun r=>(RingHom.congr_fun hb r).symm}
  have hh:fA=gA:=hom_ext a h
  exact congrArg AlgHom.toRingHom hh
end ThreeRootCoordinates318
