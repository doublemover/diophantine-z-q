module
public import FourRootDualityBaseChange318
public import FourRootUnitScale318
public section
noncomputable section
namespace FourRootDualityUnitScale318
open FourRootIntegralDuality318 FourRootTraceCoefficient318 QuadraticIntegralDuality318
open scoped TensorProduct
set_option maxHeartbeats 2400000
variable {R : Type*} [CommRing R] (a b : Fin 4 → R) (s : Rˣ)
  (h : ∀ i,b i=a i*(s:R)^2)

/-- Exact highest-coefficient change under the actual marked-root unit
scaling. Four roots contribute four powers, not an inferred sign or degree. -/
theorem coefficient_scale (x : FourRootOrder318.Order b) :
    coefficient a (FourRootUnitScale318.four a b s h x)=
      (s:R)^4 * coefficient b x := by
  have hb (i : Index) : coefficient a
      (FourRootUnitScale318.four a b s h ((frame b).basis i))=
        (s:R)^4*coefficient b ((frame b).basis i) := by
    rcases i with ⟨⟨i,j⟩,⟨k,l⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [frame,TensorCoefficientDuality318.Frame.tensor,Module.Basis.tensorProduct_apply,
        root_basis_zero,root_basis_one,FourRootUnitScale318.four,
        Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
        FourRootUnitScale318.root_scale,coefficient,
        TensorCoefficientDuality318.Frame.tensorCoefficient_tmul,
        TensorProduct.smul_tmul',TensorProduct.tmul_smul,
        rootCoefficient_one,rootCoefficient_root,map_smul,smul_eq_mul] <;> ring
  conv_lhs => rw [←(frame b).basis.sum_repr x]
  rw [map_sum,map_sum]
  simp_rw [map_smul,map_smul,hb,smul_eq_mul]
  conv_rhs => rw [←(frame b).basis.sum_repr x]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Literal equality of entire R-linear coefficient functionals after
transport by the whole marked-order equivalence. -/
theorem coefficient_linearMap :
    (coefficient a).comp (FourRootUnitScale318.four a b s h).toLinearMap =
      (s:R)^4 • coefficient b := by
  ext x
  exact coefficient_scale a b s h x

/-- The inverse transition of the actual dual generator. This is proved
on all elements of the whole order and needs no generic trace inversion. -/
theorem coefficient_inverse (x : FourRootOrder318.Order b) :
    coefficient b x=(↑s⁻¹:R)^4*
      coefficient a (FourRootUnitScale318.four a b s h x) := by
  rw [coefficient_scale,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]
end FourRootDualityUnitScale318
