module
public import FourRootRatioOrder318
public import FourRootMonomialCoefficient318
public section
noncomputable section
namespace FourRootRatioDualCoefficient318
open FourRootRatioOrder318 FourRootOrderSigns318 FourRootIntegralDuality318
open FourRootDualityBaseChange318 FourRootMonomialCoefficient318 QuadraticIntegralDuality318
set_option maxHeartbeats 1800000
variable {R : Type*} [CommRing R] (q : R) (r : Fin 3 → R)

lemma map_basis (i : Index) : map q r ((frame (original q r)).basis i)=
    generator (normalized q r) 0^(i.1.1.val+i.1.2.val+i.2.1.val+i.2.2.val)*
      generator (normalized q r) 1^i.1.2.val * generator (normalized q r) 2^i.2.1.val *
      generator (normalized q r) 3^i.2.2.val := by
  rw [basis_monomial]
  simp only [map_mul,map_pow,map_root,marked,Fin.cases_zero,Fin.cases_succ,mul_pow,pow_add]
  ring

lemma root_basis (i : Index) : generator (original q r) 0 * (frame (original q r)).basis i =
    generator (original q r) 0^(1+i.1.1.val) * generator (original q r) 1^i.1.2.val *
      generator (original q r) 2^i.2.1.val * generator (original q r) 3^i.2.2.val := by
  rw [basis_monomial,pow_add,pow_one]
  ring

/-- The normalization discrepancy is proved on the entire actual order:
restriction of the ratio-order dual generator is q*y0 times the original
one, equivalently y0 cubed. No unit or characteristic hypothesis is used. -/
lemma coefficient_map (x : OriginalOrder q r) :
    coefficient (normalized q r) (map q r x)=
      q * coefficient (original q r) (generator (original q r) 0*x) := by
  have hb (i : Index) : coefficient (normalized q r) (map q r ((frame (original q r)).basis i))=
      q * coefficient (original q r) (generator (original q r) 0*(frame (original q r)).basis i) := by
    rw [map_basis,root_basis,coefficient_monomial,coefficient_monomial]
    rcases i with ⟨⟨i,j⟩,⟨k,l⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [original,normalized,rootCoefficient_one,rootCoefficient_root,
        rootCoefficient_square,rootCoefficient_cube,rootCoefficient_fourth]
  conv_lhs => rw [←(frame (original q r)).basis.sum_repr x]
  simp only [map_sum,map_smul,smul_eq_mul,hb]
  conv_rhs => rw [←(frame (original q r)).basis.sum_repr x]
  simp only [Finset.mul_sum,map_sum,mul_smul_comm,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma coefficient_map_cube (x : OriginalOrder q r) :
    coefficient (normalized q r) (map q r x)=
      coefficient (original q r) (generator (original q r) 0^3*x) := by
  rw [coefficient_map]
  rw [show (3:ℕ)=2+1 from rfl,pow_add,generator_square,pow_one]
  change q * coefficient (original q r) (generator (original q r) 0*x) =
    coefficient (original q r) ((algebraMap R (OriginalOrder q r) q*generator (original q r) 0)*x)
  rw [mul_assoc,←Algebra.smul_def,map_smul,smul_eq_mul]

/-- Equality of whole R-linear dual maps, not only their values at a
selected arithmetic point or a chosen generic frame. -/
lemma dual_restriction :
    (coefficient (normalized q r)).comp (map q r).toLinearMap =
      (FourRootIntegralDuality318.duality (original q r)
        (generator (original q r) 0^3)) := by
  ext x
  exact coefficient_map_cube q r x
end FourRootRatioDualCoefficient318
