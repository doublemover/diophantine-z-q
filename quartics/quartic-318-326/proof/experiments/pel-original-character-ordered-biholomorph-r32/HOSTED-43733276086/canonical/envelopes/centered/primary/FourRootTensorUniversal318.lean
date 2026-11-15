module
public import FourRootSignBaseChange318
public section
noncomputable section
namespace FourRootTensorUniversal318
open scoped TensorProduct
open QuadraticPresentation318 FourRootOrder318 FourRootOrderSigns318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (a:Fin 4→R) (z:Fin 4→S) (hz:∀k,z k^2=algebraMap R S (a k))

@[expose] def rootHom (k:Fin 4):RootRing (a k)→ₐ[R]S:=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) (z k) (by
    change Polynomial.aeval (z k) (Polynomial.X^2-Polynomial.C (a k))=0
    simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,hz,sub_self])

@[simp] theorem rootHom_root (k:Fin 4):
    rootHom a z hz k (AdjoinRoot.root (polynomial (a k)))=z k:=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def lift:Order a→ₐ[R]S:=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (rootHom a z hz 0) (rootHom a z hz 1) (fun _ _=>Commute.all _ _))
    (Algebra.TensorProduct.lift (rootHom a z hz 2) (rootHom a z hz 3) (fun _ _=>Commute.all _ _))
    (fun _ _=>Commute.all _ _)

@[simp] theorem lift_generator (k:Fin 4):lift a z hz (generator a k)=z k:=by
  fin_cases k <;> simp [generator,lift,Algebra.TensorProduct.lift_tmul]

/-- Ring maps need both the actual coefficient action and four root values;
no implicit replacement polynomial-base algebra is used. -/
theorem ringHom_ext {T:Type*} [CommRing T] {f g:Order a→+*T}
    (hc:f.comp (algebraMap R (Order a))=g.comp (algebraMap R (Order a)))
    (h:∀k,f (generator a k)=g (generator a k)):f=g:=by
  letI:Algebra R T:=(f.comp (algebraMap R (Order a))).toAlgebra
  let fA:Order a→ₐ[R]T:={f with commutes':=fun _=>rfl}
  let gA:Order a→ₐ[R]T:={g with commutes':=fun r=>(RingHom.congr_fun hc r).symm}
  have he:fA=gA:=FourRootSignBaseChange318.hom_ext a h
  exact congrArg AlgHom.toRingHom he
end FourRootTensorUniversal318
