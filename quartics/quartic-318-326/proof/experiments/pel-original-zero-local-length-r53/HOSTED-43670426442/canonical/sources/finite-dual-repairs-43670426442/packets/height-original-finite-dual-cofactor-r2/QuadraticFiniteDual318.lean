module
public import QuadraticPresentation318
public import Mathlib.LinearAlgebra.Dual.Defs
public section
noncomputable section
namespace QuadraticFiniteDual318
variable (R : Type*) [CommRing R] (b : R)
local notation "Q" => QuadraticAlgebra R b 0
local notation "ω" => (QuadraticAlgebra.omega : Q)

/-- The literal coefficient functional on the actual quadratic algebra.
No inversion of2, the radicand or the root is used. -/
@[expose] def residue : Module.Dual R Q := QuadraticAlgebra.imₗ b 0

@[expose] def pairing : Q →ₗ[R] Module.Dual R Q where
  toFun x :=
    { toFun := fun y => (x*y).im
      map_add' := fun y z => by rw [mul_add,QuadraticAlgebra.im_add]
      map_smul' := fun r y => by
        change (x*(r • y)).im=r • (x*y).im
        rw [mul_smul_comm,QuadraticAlgebra.im_smul] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change ((x+y)*z).im=(x*z).im+(y*z).im
    rw [add_mul,QuadraticAlgebra.im_add]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change ((r • x)*y).im=r • (x*y).im
    rw [smul_mul_assoc,QuadraticAlgebra.im_smul]

theorem pairing_apply (x y : Q) : pairing R b x y=residue R b (x*y) := rfl

/-- Perfect finite-algebra duality over an arbitrary commutative base,
including nonunit radicands and residue characteristic2. The target is the
ACTUAL Hom_R(Q,R), not a free module declared to be dualizing. -/
@[expose] def perfect : Q ≃ₗ[R] Module.Dual R Q where
  __ := pairing R b
  invFun φ := ⟨φ ω,φ 1⟩
  left_inv x := by
    apply QuadraticAlgebra.ext
    · change (x*ω).im=x.re
      simp [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega]
    · change (x*1).im=x.im
      rw [mul_one]
  right_inv φ := by
    apply LinearMap.ext
    intro x
    have hx := congrArg φ (QuadraticAlgebra.re_smul_add_im_smul x)
    rw [map_add,map_smul,map_smul] at hx
    change (pairing R b (⟨φ ω,φ 1⟩ : Q)) x=φ x
    calc
      (pairing R b (⟨φ ω,φ 1⟩ : Q)) x=x.re*φ 1+x.im*φ ω := by
        change φ ω*x.im+φ 1*x.re+0*φ 1*x.im=_
        ring
      _=φ x := by simpa only [smul_eq_mul] using hx

/-- Equivariance under the ACTUAL multiplication/precomposition action
on Hom_R(Q,R), stated explicitly without hiding a chosen module instance. -/
theorem perfect_mul (x y z : Q) : perfect R b (x*y) z=perfect R b x (y*z) := by
  change ((x*y)*z).im=(x*(y*z)).im
  rw [mul_assoc]

/-- Native quadratic trace is the perfect dual generator multiplied by
the exact different factor2ω. This factor is not canceled at bad primes. -/
theorem trace_different (x : Q) :
    QuadraticAlgebra.trace x=perfect R b (2*ω) x := by
  change 2*x.re+0*x.im=((2*ω)*x).im
  simp [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_mul,
    QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega,
    QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

/-- Transport of the perfect pairing to the original monic quotient,
using its actual algebra presentation equivalence in both arguments. -/
@[expose] def rootPerfect : QuadraticPresentation318.RootRing b ≃ₗ[R]
    Module.Dual R (QuadraticPresentation318.RootRing b) :=
  (QuadraticPresentation318.presentationEquiv b).symm.toLinearEquiv.trans
    ((perfect R b).trans (QuadraticPresentation318.presentationEquiv b).symm.toLinearEquiv.dualMap)

theorem rootPerfect_apply (x y : QuadraticPresentation318.RootRing b) :
    rootPerfect R b x y=
      ((QuadraticPresentation318.presentationEquiv b).symm (x*y)).im := by
  change (((QuadraticPresentation318.presentationEquiv b).symm x)*
    ((QuadraticPresentation318.presentationEquiv b).symm y)).im=_
  rw [map_mul]

theorem rootPerfect_mul (x y z : QuadraticPresentation318.RootRing b) :
    rootPerfect R b (x*y) z=rootPerfect R b x (y*z) := by
  rw [rootPerfect_apply,rootPerfect_apply,mul_assoc]
end QuadraticFiniteDual318
