module
public import FourRootOrderSigns318
public section
noncomputable section
namespace FourRootSignBaseChange318
open scoped TensorProduct
open QuadraticPresentation318 FourRootOrder318 FourRootOrderSigns318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] (a:Fin 4→R)
variable {T:Type*} [CommRing T] [Algebra R T]
/-- All four actual tensor generators determine an algebra map. -/
theorem hom_ext {f g:Order a→ₐ[R]T}
    (h:∀i,f (generator a i)=g (generator a i)):f=g:=by
  apply Algebra.TensorProduct.ext
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 0
    · apply AdjoinRoot.algHom_ext
      exact h 1
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 2
    · apply AdjoinRoot.algHom_ext
      exact h 3

variable (S:Type*) [CommRing S] [Algebra R S]
/-- The literal coefficient-change embedding into the actual base-changed order. -/
@[expose] def coefficientMap:Order a→ₐ[R]Order (fun i=>algebraMap R S (a i)):=
  ((baseChange a S).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem coefficientMap_generator (i:Fin 4):
    coefficientMap a S (generator a i)=generator (fun i=>algebraMap R S (a i)) i:=by
  fin_cases i <;>
    simp [coefficientMap,baseChange,pairBaseChange,generator,TensorPairBaseChange318.split_one,
      ContactGenericFiber318.rootBaseChange_generator] <;>
    simp only [←Algebra.TensorProduct.one_def,map_one]

theorem sign_coefficientMap (b:Fin 4→Bool):
    (coefficientMap a S).comp (signEquiv a b).toAlgHom=
      ((signEquiv (fun i=>algebraMap R S (a i)) b).toAlgHom.restrictScalars R).comp
        (coefficientMap a S):=by
  apply hom_ext
  intro i
  change coefficientMap a S (signEquiv a b (generator a i))=
    signEquiv (fun i=>algebraMap R S (a i)) b (coefficientMap a S (generator a i))
  rw [coefficientMap_generator,signEquiv_generator,signEquiv_generator]
  cases hb:b i <;> simp [hb,coefficientMap_generator]
end FourRootSignBaseChange318
