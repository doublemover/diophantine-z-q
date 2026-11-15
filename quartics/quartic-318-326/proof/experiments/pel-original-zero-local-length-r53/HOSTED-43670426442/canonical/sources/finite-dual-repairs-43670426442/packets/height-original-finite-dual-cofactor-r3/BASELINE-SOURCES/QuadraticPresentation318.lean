module
public import Mathlib.Algebra.QuadraticAlgebra.BaseChange
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic
public section
noncomputable section
namespace QuadraticPresentation318
set_option maxHeartbeats 300000
open Polynomial
variable {R:Type*} [CommRing R]

@[expose] def polynomial (b:R):R[X]:=X^2-C b
abbrev RootRing (b:R):=AdjoinRoot (polynomial b)

theorem root_square (b:R) : (AdjoinRoot.root (polynomial b))^2=algebraMap R (RootRing b) b := by
  have h:=AdjoinRoot.mk_self (f:=polynomial b)
  change AdjoinRoot.mk (polynomial b) (X^2-C b)=0 at h
  rw [map_sub,map_pow,AdjoinRoot.mk_X,AdjoinRoot.mk_C,sub_eq_zero] at h
  exact h

@[expose] def toRoot (b:R) : QuadraticAlgebra R b 0→ₐ[R]RootRing b :=
  QuadraticAlgebra.lift ⟨AdjoinRoot.root (polynomial b),by
    simpa only [←pow_two,zero_smul,add_zero,Algebra.smul_def,mul_one,map_zero,zero_mul,add_zero] using root_square b⟩

@[expose] def fromRoot (b:R) : RootRing b→ₐ[R]QuadraticAlgebra R b 0 :=
  AdjoinRoot.liftAlgHom (polynomial b) (Algebra.ofId R _) QuadraticAlgebra.omega (by
    change Polynomial.aeval (QuadraticAlgebra.omega:QuadraticAlgebra R b 0) (polynomial b)=0
    simp only [polynomial,map_sub,map_pow,aeval_X,aeval_C]
    rw [QuadraticAlgebra.omega_pow_two_eq_add,zero_smul,add_zero,Algebra.smul_def,mul_one,sub_self])

@[simp] theorem toRoot_generator (b:R) : toRoot b QuadraticAlgebra.omega=AdjoinRoot.root (polynomial b) := by
  change QuadraticAlgebra.lift _ QuadraticAlgebra.omega = _
  simp only [QuadraticAlgebra.lift_apply_apply,QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega,zero_smul,one_smul,zero_add]

@[simp] theorem fromRoot_generator (b:R) : fromRoot b (AdjoinRoot.root (polynomial b))=QuadraticAlgebra.omega :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def presentationEquiv (b:R) : QuadraticAlgebra R b 0≃ₐ[R]RootRing b where
  __ := toRoot b
  invFun:=fromRoot b
  left_inv z:=by
    have h:(fromRoot b).comp (toRoot b)=AlgHom.id R _ := by
      apply QuadraticAlgebra.algHom_ext
      simp
    exact AlgHom.congr_fun h z
  right_inv z:=by
    have h:(toRoot b).comp (fromRoot b)=AlgHom.id R _ := by
      apply AdjoinRoot.algHom_ext
      simp
    exact AlgHom.congr_fun h z

@[simp] theorem presentationEquiv_generator (b:R) :
    presentationEquiv b QuadraticAlgebra.omega=AdjoinRoot.root (polynomial b) := toRoot_generator b

end QuadraticPresentation318
