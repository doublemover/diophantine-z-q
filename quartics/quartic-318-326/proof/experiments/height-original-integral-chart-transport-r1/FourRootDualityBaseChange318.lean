module
public import FourRootTraceCoefficient318
public import FourRootSignBaseChange318
public section
noncomputable section
namespace FourRootDualityBaseChange318
open FourRootIntegralDuality318 FourRootTraceCoefficient318 FourRootSignBaseChange318
open QuadraticIntegralDuality318
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : Fin 4 → R)

/-- The displayed duality basis is literally the original squarefree
monomials in the four marked generators, not a chosen abstract basis. -/
theorem basis_monomial (i : Index) : (frame a).basis i =
    FourRootOrderSigns318.generator a 0 ^ i.1.1.val *
      FourRootOrderSigns318.generator a 1 ^ i.1.2.val *
      FourRootOrderSigns318.generator a 2 ^ i.2.1.val *
      FourRootOrderSigns318.generator a 3 ^ i.2.2.val := by
  rcases i with ⟨⟨i,j⟩,⟨k,l⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [frame,TensorCoefficientDuality318.Frame.tensor,Module.Basis.tensorProduct_apply,
      root_basis_zero,root_basis_one,FourRootOrderSigns318.generator,
      Algebra.TensorProduct.one_def,Algebra.TensorProduct.tmul_mul_tmul]

theorem coefficientMap_basis (i : Index) :
    coefficientMap a S ((frame a).basis i)=
      (frame (fun j => algebraMap R S (a j))).basis i := by
  rw [basis_monomial,basis_monomial]
  simp only [map_mul,map_pow,coefficientMap_generator]

theorem coefficient_basis_map (i : Index) :
    coefficient (fun j => algebraMap R S (a j))
        ((frame (fun j => algebraMap R S (a j))).basis i)=
      algebraMap R S (coefficient a ((frame a).basis i)) := by
  rcases i with ⟨⟨i,j⟩,⟨k,l⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [frame,TensorCoefficientDuality318.Frame.tensor,Module.Basis.tensorProduct_apply,
      coefficient,TensorCoefficientDuality318.Frame.tensorCoefficient_tmul,
      root_basis_zero,root_basis_one,rootCoefficient_one,rootCoefficient_root]

/-- The highest-root coefficient commutes with the actual whole-order
coefficient map, with the literal base scalar map on the right. -/
theorem coefficientMap_coefficient (x : FourRootOrder318.Order a) :
    coefficient (fun j => algebraMap R S (a j)) (coefficientMap a S x)=
      algebraMap R S (coefficient a x) := by
  conv_lhs => rw [←(frame a).basis.sum_repr x]
  conv_rhs => rw [←(frame a).basis.sum_repr x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,coefficientMap_basis,
    ←IsScalarTower.algebraMap_smul R S (FourRootOrder318.Order (fun j => algebraMap R S (a j))),
    map_smul,coefficient_basis_map,map_smul,smul_eq_mul,map_mul]
  rfl

end FourRootDualityBaseChange318
