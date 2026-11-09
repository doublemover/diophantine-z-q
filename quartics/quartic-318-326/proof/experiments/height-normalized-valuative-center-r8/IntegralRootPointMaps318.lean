module
public import FourRootSignBaseChange318
public import ThreeRootCoordinates318
public section
noncomputable section
namespace IntegralRootPointMaps318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]

@[expose] def rootMap (a : A) (z : T) (hz : z^2=algebraMap A T a) :
    RootRing a →ₐ[A] T :=
  AdjoinRoot.liftAlgHom (polynomial a) (Algebra.ofId A T) z (by
    change Polynomial.aeval z (X^2-C a)=0
    simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,hz,sub_self])

theorem rootMap_root (a : A) (z : T) (hz : z^2=algebraMap A T a) :
    rootMap a z hz (AdjoinRoot.root (polynomial a))=z :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def fourMap (a : Fin 4 → A) (z : Fin 4 → T)
    (hz : ∀ i, (z i)^2=algebraMap A T (a i)) : FourRootOrder318.Order a →ₐ[A] T :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (rootMap (a 0) (z 0) (hz 0))
      (rootMap (a 1) (z 1) (hz 1)) (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift (rootMap (a 2) (z 2) (hz 2))
      (rootMap (a 3) (z 3) (hz 3)) (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

theorem fourMap_generator (a : Fin 4 → A) (z : Fin 4 → T)
    (hz : ∀ i, (z i)^2=algebraMap A T (a i)) (i : Fin 4) :
    fourMap a z hz (FourRootOrderSigns318.generator a i)=z i := by
  fin_cases i <;> simp only [fourMap,FourRootOrderSigns318.generator,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Algebra.TensorProduct.lift_tmul,
    map_one,mul_one,one_mul,rootMap_root]

@[expose] def threeMap (a : Fin 3 → A) (z : Fin 3 → T)
    (hz : ∀ i, (z i)^2=algebraMap A T (a i)) : ThreeRootOrder318.Order a →ₐ[A] T :=
  Algebra.TensorProduct.lift (rootMap (a 0) (z 0) (hz 0))
    (Algebra.TensorProduct.lift (rootMap (a 1) (z 1) (hz 1))
      (rootMap (a 2) (z 2) (hz 2)) (fun _ _ => Commute.all _ _)) (fun _ _ => Commute.all _ _)

theorem threeMap_generator (a : Fin 3 → A) (z : Fin 3 → T)
    (hz : ∀ i, (z i)^2=algebraMap A T (a i)) (i : Fin 3) :
    threeMap a z hz (ThreeRootCoordinates318.generator a i)=z i := by
  fin_cases i <;> simp only [threeMap,ThreeRootCoordinates318.generator,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Algebra.TensorProduct.lift_tmul,
    map_one,mul_one,one_mul,rootMap_root]

/-- Equality on coefficients and ALL original signed roots gives equality
of the entire original source point, not just its projective coordinate. -/
theorem four_ringHom_ext {a : Fin 4 → A} {f g : FourRootOrder318.Order a →+* T}
    (hb : f.comp (algebraMap A (FourRootOrder318.Order a))=
      g.comp (algebraMap A (FourRootOrder318.Order a)))
    (hz : ∀ i, f (FourRootOrderSigns318.generator a i)=g (FourRootOrderSigns318.generator a i)) : f=g := by
  letI : Algebra A T := (f.comp (algebraMap A (FourRootOrder318.Order a))).toAlgebra
  let fA : FourRootOrder318.Order a →ₐ[A] T := {f with commutes' := fun _ => rfl}
  let gA : FourRootOrder318.Order a →ₐ[A] T :=
    {g with commutes' := fun r => (RingHom.congr_fun hb r).symm}
  have hh : fA=gA := FourRootSignBaseChange318.hom_ext a hz
  exact congrArg AlgHom.toRingHom hh
end IntegralRootPointMaps318
