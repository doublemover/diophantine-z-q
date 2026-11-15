module
public import OddTwistDilatationSourceMap318
public import FourRootPivot318
public section
noncomputable section
namespace FinitePivotCanonicalSource318
open Polynomial FourRootPivot318 OddTwistDilatationEtale318
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4)
@[expose] def indexEquiv : Fin 4 ≃ Fin 4 where
  toFun := indices i
  invFun := ![![0,1,2,3],![1,0,2,3],![2,3,0,1],![2,3,1,0]] i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide
@[expose] abbrev others (f : Fin 4 → V) (pivot : Fin 4) : Fin 3 → V := fun j => f (indices pivot j.succ)
@[expose] abbrev Chart := OddTwistDilatationEtale318.Chart V rho u (a i) (others V d i) (others V a i)
local notation "C" => Chart V rho u d a i
@[expose] def originalRoot (k : Fin 4) : C :=
  OddTwistDilatationSourceMap318.originalRoot V rho u (a i) (others V d i) (others V a i)
    ((indexEquiv i).symm k)
lemma originalRoot_index (j : Fin 4) : originalRoot V rho u d a i (indices i j)=
    OddTwistDilatationSourceMap318.originalRoot V rho u (a i) (others V d i) (others V a i) j := by
  change _ ((indexEquiv i).symm ((indexEquiv i) j))=_
  rw [Equiv.symm_apply_apply]
@[expose] def scalarMap : V[X] →+* C :=
  OddTwistDilatationSourceMap318.originalScalar V rho u (a i) (others V d i) (others V a i)
variable (hd : d i=(u:V)*rho)
include hd in
lemma root_square (k : Fin 4) : (originalRoot V rho u d a i k)^2=
    scalarMap V rho u d a i (DVRNormalizedFiniteOrder318.coefficient V d a k) := by
  obtain ⟨j,rfl⟩ := (indexEquiv i).surjective k
  change (originalRoot V rho u d a i (indices i j))^2=_
  rw [originalRoot_index,OddTwistDilatationSourceMap318.original_root_square]
  apply congrArg (scalarMap V rho u d a i)
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [OddTwistDilatationSourceMap318.originalCoefficient,Fin.cases_zero,
      DVRNormalizedFiniteOrder318.coefficient,indices_zero,hd]
  · rfl
/-- Whole ORIGINAL order map, with all root indices restored before the
finite-dual or bicanonical comparison. No orientation shortcut is used. -/
@[expose] def sourceMap : DVRNormalizedFiniteOrder318.Order V d a →+* C := by
  letI : Algebra V[X] C := (scalarMap V rho u d a i).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ (originalRoot V rho u d a i)
    (root_square V rho u d a i hd)).toRingHom
lemma sourceMap_polynomial (p : V[X]) : sourceMap V rho u d a i hd
    (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V d a) p)=scalarMap V rho u d a i p := by
  letI : Algebra V[X] C := (scalarMap V rho u d a i).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ (originalRoot V rho u d a i)
    (root_square V rho u d a i hd)).commutes p
lemma sourceMap_root (k : Fin 4) : sourceMap V rho u d a i hd
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) k)=
      originalRoot V rho u d a i k := by
  letI : Algebra V[X] C := (scalarMap V rho u d a i).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ k

lemma product_pivot (f : Fin 4 → V) : (∏k:Fin 4,f k)=f i*∏j:Fin 3,f (indices i j.succ) := by
  fin_cases i <;> simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,indices,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,one_mul,mul_one] <;> ring
end FinitePivotCanonicalSource318
