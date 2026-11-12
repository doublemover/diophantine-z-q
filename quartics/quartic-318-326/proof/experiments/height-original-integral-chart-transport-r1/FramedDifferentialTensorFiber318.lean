module
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public section
noncomputable section
namespace FramedDifferentialTensorFiber318
open scoped TensorProduct
variable {A V M : Type*} [CommRing A] [CommRing V] [AddCommGroup M] [Module A M]
  (e : A →+* V) (F : M ≃ₗ[A] A)
@[expose] def frame : M →ₛₗ[e] V where
  toFun m := e (F m)
  map_add' m n := by rw [map_add,map_add]
  map_smul' a m := by rw [map_smul]; change e (a*F m)=e a*e (F m); rw [map_mul]
@[expose] def balanced : M →ₛₗ[e] M →ₛₗ[e] V where
  toFun m :=
    { toFun := fun n => frame e F m*frame e F n
      map_add' := fun n p => by rw [map_add,mul_add]
      map_smul' := fun a n => by rw [LinearMap.map_smulₛₗ]; simp only [smul_eq_mul]; ring }
  map_add' m n := by
    ext p
    change frame e F (m+n)*frame e F p=frame e F m*frame e F p+frame e F n*frame e F p
    rw [map_add,add_mul]
  map_smul' a m := by
    ext n
    change frame e F (a • m)*frame e F n=e a*(frame e F m*frame e F n)
    rw [LinearMap.map_smulₛₗ]
    simp only [smul_eq_mul]
    ring
/-- An actual balanced map on the full tensor square, not a functional
on chosen pure-tensor presentations. -/
@[expose] def tensorFiber : (M ⊗[A] M) →ₛₗ[e] V := TensorProduct.lift (balanced e F)
lemma tensorFiber_tmul (m n : M) : tensorFiber e F (m ⊗ₜ[A] n)=frame e F m*frame e F n :=
  TensorProduct.lift.tmul _ _ _
lemma tensorFiber_weighted (k : A) (m : M) (hm : F m=1) :
    tensorFiber e F (k • (m ⊗ₜ[A] m))=e k := by
  rw [LinearMap.map_smulₛₗ,tensorFiber_tmul]
  change e k*(e (F m)*e (F m))=e k
  rw [hm,map_one,mul_one,mul_one]
end FramedDifferentialTensorFiber318
