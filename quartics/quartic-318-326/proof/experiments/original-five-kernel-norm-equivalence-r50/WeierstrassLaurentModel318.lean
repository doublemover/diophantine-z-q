module
public import InfinityMonicPresentation318
public import WeierstrassBoundaryClass318
public import Mathlib.Algebra.Polynomial.Laurent

public section
noncomputable section
namespace WeierstrassLaurentModel318
open Polynomial
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Coeff := LaurentPolynomial ℚ
variable (A B : ℚ)

/-- The literal infinity equation, now over the invertible original z coordinate. -/
@[expose] def polynomial : Coeff[X] := X^3 +
  (C (LaurentPolynomial.C A * LaurentPolynomial.T 2) * X +
    C (LaurentPolynomial.C B * LaurentPolynomial.T 3 - LaurentPolynomial.T 1))

theorem monic : (polynomial A B).Monic := by
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _)
    norm_num
  · apply lt_of_le_of_lt Polynomial.degree_C_le
    norm_num

theorem degree : (polynomial A B).natDegree = 3 := by
  unfold polynomial
  compute_degree!

abbrev Model := AdjoinRoot (polynomial A B)
@[expose] def x : Model A B := AdjoinRoot.root (polynomial A B)
@[expose] def zpow (n : ℤ) : Model A B := algebraMap Coeff (Model A B) (LaurentPolynomial.T n)

@[expose] def basis : Module.Basis (Fin 3) Coeff (Model A B) :=
  (AdjoinRoot.powerBasis' (monic A B)).basis.reindex (finCongr (degree A B))

theorem basis_apply (i : Fin 3) : basis A B i = x A B ^ (i : ℕ) := by
  rw [basis,Module.Basis.reindex_apply,PowerBasis.basis_eq_pow]
  all_goals rfl

theorem zpow_add (m n : ℤ) : zpow A B (m+n) = zpow A B m * zpow A B n := by
  simp only [zpow,LaurentPolynomial.T_add,map_mul]

theorem zpow_zero : zpow A B 0 = 1 := by rw [zpow,LaurentPolynomial.T_zero,map_one]

theorem zpow_mul (m n : ℤ) : zpow A B m * zpow A B n = zpow A B (m+n) :=
  (zpow_add A B m n).symm

theorem relation : x A B ^ 3 = zpow A B 1 -
    algebraMap ℚ (Model A B) A * x A B * zpow A B 2 -
    algebraMap ℚ (Model A B) B * zpow A B 3 := by
  have h := AdjoinRoot.eval₂_root (polynomial A B)
  change (polynomial A B).eval₂ (algebraMap Coeff (Model A B)) (x A B) = 0 at h
  simp only [polynomial,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,map_mul,map_sub] at h
  have hc (q : ℚ) : algebraMap Coeff (Model A B) (LaurentPolynomial.C q) =
      algebraMap ℚ (Model A B) q := by
    exact (IsScalarTower.algebraMap_apply ℚ Coeff (Model A B) q).symm
  simp only [hc] at h
  change x A B^3 + (algebraMap ℚ (Model A B) A * zpow A B 2 * x A B +
    (algebraMap ℚ (Model A B) B * zpow A B 3 - zpow A B 1)) = 0 at h
  linear_combination h

/-- Exact map from the original whole infinity ring, fixed on both original generators. -/
@[expose] def infinityMap : InfinityChart318.Ring A B →ₐ[ℚ] Model A B :=
  InfinityChart318.lift A B (x A B) (zpow A B 1) (by
    have h2 : zpow A B 1 ^ 2 = zpow A B 2 := by
      rw [pow_two,zpow_mul]; norm_num
    have h3 : zpow A B 1 ^ 3 = zpow A B 3 := by
      rw [pow_succ,h2,zpow_mul]; norm_num
    rw [h2,h3]
    linear_combination -(relation A B))

@[simp] theorem infinityMap_x : infinityMap A B (InfinityChart318.x A B) = x A B :=
  InfinityChart318.lift_x ..
@[simp] theorem infinityMap_z : infinityMap A B (InfinityChart318.z A B) = zpow A B 1 :=
  InfinityChart318.lift_z ..

/-- Actual localization map from the old common-open ring. No injectivity is assumed or needed. -/
@[expose] def overlapMap : WeierstrassOverlap318.InfinityOverlap A B →ₐ[ℚ] Model A B :=
  IsLocalization.Away.liftAlgHom (f:=infinityMap A B) (InfinityChart318.z A B) (by
    rw [infinityMap_z]
    exact (LaurentPolynomial.isUnit_T 1).map (algebraMap Coeff (Model A B)))

theorem overlapMap_base (a : InfinityChart318.Ring A B) :
    overlapMap A B (algebraMap (InfinityChart318.Ring A B) _ a) = infinityMap A B a := by
  simp only [overlapMap,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem overlapMap_ix : overlapMap A B (WeierstrassOverlap318.ix A B) = x A B := by
  rw [WeierstrassOverlap318.ix,overlapMap_base,infinityMap_x]
@[simp] theorem overlapMap_iz : overlapMap A B (WeierstrassOverlap318.iz A B) = zpow A B 1 := by
  rw [WeierstrassOverlap318.iz,overlapMap_base,infinityMap_z]
@[simp] theorem overlapMap_ii : overlapMap A B (WeierstrassOverlap318.ii A B) = zpow A B (-1) := by
  have h := congrArg (overlapMap A B) (WeierstrassOverlap318.iz_ii A B)
  rw [map_mul,map_one,overlapMap_iz] at h
  calc
    _ = zpow A B (-1) * (zpow A B 1 * overlapMap A B (WeierstrassOverlap318.ii A B)) := by
      rw [← mul_assoc,zpow_mul]; norm_num [zpow_zero]
    _ = _ := by rw [h,mul_one]

@[expose] def finiteMap : ShortAffineJacobian318.Ring A B →ₐ[ℚ] Model A B :=
  (overlapMap A B).comp (WeierstrassOverlap318.toInfinityBase A B)
@[simp] theorem finiteMap_x : finiteMap A B (ShortAffineJacobian318.x A B) =
    x A B * zpow A B (-1) := by
  simp only [finiteMap,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_x,map_mul,
    overlapMap_ix,overlapMap_ii]
@[simp] theorem finiteMap_y : finiteMap A B (ShortAffineJacobian318.y A B) = zpow A B (-1) := by
  simp only [finiteMap,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y,overlapMap_ii]

@[expose] def monomial (n : ℤ) (i : Fin 3) : Model A B := zpow A B n * x A B^(i:ℕ)

theorem monomial_smul (n : ℤ) (i : Fin 3) : monomial A B n i =
    (LaurentPolynomial.T n : Coeff) • basis A B i := by
  rw [basis_apply,Algebra.smul_def]
  all_goals rfl

/-- Extraction of the x²z⁻¹ coefficient in the genuine rank-three Laurent model. -/
@[expose] def residue : Model A B →ₗ[ℚ] ℚ where
  toFun a := ((basis A B).repr a 2).coeff (-1)
  map_add' a b := by simp
  map_smul' q a := by
    have h := ((basis A B).repr.restrictScalars ℚ).map_smul q a
    change (basis A B).repr (q • a) = q • (basis A B).repr a at h
    rw [h]
    rfl

theorem residue_monomial (n : ℤ) (i : Fin 3) :
    residue A B (monomial A B n i) = if i = 2 ∧ n = -1 then 1 else 0 := by
  rw [monomial_smul]
  change (((basis A B).repr ((LaurentPolynomial.T n : Coeff) • basis A B i)) 2).coeff (-1) = _
  simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul]
  by_cases hi : i = 2 <;> simp [hi,LaurentPolynomial.T_apply]

end WeierstrassLaurentModel318
