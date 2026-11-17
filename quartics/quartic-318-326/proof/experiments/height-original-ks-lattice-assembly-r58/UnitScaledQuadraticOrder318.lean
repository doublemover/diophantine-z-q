module
public import IntegralGlobalBicanonicalPair318
public section
noncomputable section
namespace UnitScaledQuadraticOrder318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- Scaling the ROOT by a unit does not require the radicand to be a unit.
This map therefore retains the branch points omitted by an etale-only chart. -/
@[expose] def forward (a b : R) (y : Rˣ) (h : b=a*(y:R)^2) :
    RootRing b →ₐ[R] RootRing a :=
  AdjoinRoot.liftAlgHom (polynomial b) (Algebra.ofId R _)
    (algebraMap R (RootRing a) (y:R) * AdjoinRoot.root (polynomial a)) (by
      change Polynomial.aeval _ (X^2-C b)=0
      rw [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,mul_pow,root_square,
        ←map_pow,←map_mul]
      apply sub_eq_zero.mpr
      congr 1
      rw [h]
      ring)

@[simp] theorem forward_root (a b : R) (y : Rˣ) (h : b=a*(y:R)^2) :
    forward a b y h (AdjoinRoot.root (polynomial b))=
      algebraMap R (RootRing a) (y:R)*AdjoinRoot.root (polynomial a) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem inverse_parameter (a b : R) (y : Rˣ) (h : b=a*(y:R)^2) :
    a=b*(↑y⁻¹:R)^2 := by
  rw [h,mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one]

/-- A genuine two-sided equivalence of the full quadratic orders, even over
nonreduced bases and at zero radicands. The original root sign is fixed. -/
@[expose] def equiv (a b : R) (y : Rˣ) (h : b=a*(y:R)^2) :
    RootRing b ≃ₐ[R] RootRing a :=
  AlgEquiv.ofAlgHom (forward a b y h)
    (forward b a y⁻¹ (inverse_parameter a b y h))
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply,forward_root,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul])
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply,forward_root,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul])

@[simp] theorem equiv_root (a b : R) (y : Rˣ) (h : b=a*(y:R)^2) :
    equiv a b y h (AdjoinRoot.root (polynomial b))=
      algebraMap R (RootRing a) (y:R)*AdjoinRoot.root (polynomial a) :=
  forward_root a b y h

/-- The same root-scaling equivalence on all three original factors, without
inverting any radicand or throwing away any ramification point. -/
@[expose] def three (a b : Fin 3 → R) (y : Rˣ) (h : ∀ i,b i=a i*(y:R)^2) :
    ThreeRootOrder318.Order b ≃ₐ[R] ThreeRootOrder318.Order a :=
  Algebra.TensorProduct.congr (equiv (a 0) (b 0) y (h 0))
    (Algebra.TensorProduct.congr (equiv (a 1) (b 1) y (h 1))
      (equiv (a 2) (b 2) y (h 2)))
end UnitScaledQuadraticOrder318
