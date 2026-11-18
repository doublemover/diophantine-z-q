module
public import FourRootDualityBaseChange318
public section
noncomputable section
namespace FourRootMonomialCoefficient318
open QuadraticPresentation318 QuadraticIntegralDuality318 FourRootOrderSigns318
open FourRootIntegralDuality318
open scoped TensorProduct
variable {R : Type*} [CommRing R]

lemma rootCoefficient_scalar (a r : R) : rootCoefficient a (algebraMap R (RootRing a) r)=0 := by
  rw [show algebraMap R (RootRing a) r = r • (1 : RootRing a) from by rw [Algebra.smul_def,mul_one]]
  rw [map_smul,rootCoefficient_one,smul_zero]

lemma rootCoefficient_square (a : R) : rootCoefficient a (AdjoinRoot.root (polynomial a)^2)=0 := by
  rw [root_square,rootCoefficient_scalar]
lemma rootCoefficient_cube (a : R) : rootCoefficient a (AdjoinRoot.root (polynomial a)^3)=a := by
  rw [show (3:ℕ)=2+1 from rfl,pow_add,root_square,pow_one,←Algebra.smul_def,
    map_smul,rootCoefficient_root,smul_eq_mul,mul_one]
lemma rootCoefficient_fourth (a : R) : rootCoefficient a (AdjoinRoot.root (polynomial a)^4)=0 := by
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,root_square,←map_pow,rootCoefficient_scalar]

/-- Literal highest coefficient of every marked-root monomial, retaining
the four actual quadratic quotient coefficient maps. -/
lemma coefficient_monomial (a : Fin 4 → R) (i j k l : ℕ) :
    coefficient a (generator a 0^i * generator a 1^j * generator a 2^k * generator a 3^l)=
    (rootCoefficient (a 0) (AdjoinRoot.root (polynomial (a 0))^i)*
      rootCoefficient (a 1) (AdjoinRoot.root (polynomial (a 1))^j))*
    (rootCoefficient (a 2) (AdjoinRoot.root (polynomial (a 2))^k)*
      rootCoefficient (a 3) (AdjoinRoot.root (polynomial (a 3))^l)) := by
  simp only [generator,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Algebra.TensorProduct.one_def,Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul,one_pow,one_mul,mul_one]
  exact coefficient_pure a _ _ _ _
end FourRootMonomialCoefficient318
