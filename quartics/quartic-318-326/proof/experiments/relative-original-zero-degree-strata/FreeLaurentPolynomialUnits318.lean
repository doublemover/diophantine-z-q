module
public import FreeKernelCoefficientMap318
public import FiniteProjectiveFreeCech318
public import Mathlib.LinearAlgebra.Finsupp.Defs
public section
noncomputable section
namespace FreeLaurentPolynomialUnits318
open FiniteLaurentVectorFiltration318 LaurentPolynomial
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι] [DecidableEq ι]

local instance : Module R (ι →₀ Polynomial R) := Module.compHom _ Polynomial.C
local instance : Module R (ι →₀ LaurentPolynomial R) :=
  RelativeLaurentScalar318.coefficientModule R _

@[expose] def coordinates : (ι →₀ LaurentPolynomial R) ≃ₗ[R] V R ι :=
  { Finsupp.equivFunOnFinite with
    toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r x
      ext i
      exact (LaurentPolynomial.smul_eq_C_mul r (x i)).symm }

lemma coordinates_laurent_smul (a : LaurentPolynomial R) (x : ι →₀ LaurentPolynomial R) :
    coordinates R ι (a • x) = a • coordinates R ι x := rfl

lemma coordinates_symm_laurent_smul (a : LaurentPolynomial R) (x : V R ι) :
    (coordinates R ι).symm (a • x) = a • (coordinates R ι).symm x := by
  apply (coordinates R ι).injective
  rw [LinearEquiv.apply_symm_apply,coordinates_laurent_smul,LinearEquiv.apply_symm_apply]

lemma unit_zero (f : Polynomial R →+* LaurentPolynomial R) :
    FreeKernelCoefficientMap318.unit R f (0 : ι →₀ Polynomial R) = 0 := by
  unfold FreeKernelCoefficientMap318.unit
  rw [TensorProduct.tmul_zero,map_zero]

lemma unit_single (f : Polynomial R →+* LaurentPolynomial R) (i : ι) (p : Polynomial R) :
    FreeKernelCoefficientMap318.unit R f (Finsupp.single i p) = Finsupp.single i (f p) := by
  letI : Algebra (Polynomial R) (LaurentPolynomial R) := f.toAlgebra
  have h : (Finsupp.single i p : ι →₀ Polynomial R) = p • Finsupp.single i 1 := by simp
  rw [h,FreeKernelCoefficientMap318.unit_smul]
  change f p • OriginalFreePresentationBaseChange318.freeEquivalence (Polynomial R) (LaurentPolynomial R)
    ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] Finsupp.single i 1) = _
  rw [OriginalFreePresentationBaseChange318.freeEquivalence_basis]
  simp

@[expose] def unitMap (f : Polynomial R →+* LaurentPolynomial R)
    (hC : ∀ r : R, f (Polynomial.C r) = C r) : (ι →₀ Polynomial R) →ₗ[R] V R ι where
  toFun x := coordinates R ι (FreeKernelCoefficientMap318.unit R f x)
  map_add' x y := by rw [FreeKernelCoefficientMap318.unit_add,map_add]
  map_smul' r x := by
    change coordinates R ι (FreeKernelCoefficientMap318.unit R f ((Polynomial.C r) • x)) = _
    rw [FreeKernelCoefficientMap318.unit_smul,hC]
    exact (coordinates R ι).map_smul r _

@[expose] def positiveUnit : (ι →₀ Polynomial R) →ₗ[R] V R ι :=
  unitMap R ι Polynomial.toLaurent Polynomial.toLaurent_C
@[expose] def reciprocalUnit : (ι →₀ Polynomial R) →ₗ[R] V R ι :=
  unitMap R ι ((invert (R := R)).toRingHom.comp Polynomial.toLaurent)
    (fun r => by rw [RingHom.comp_apply,Polynomial.toLaurent_C,invert_C])
@[expose] def vectorShift (a : ℤ) : V R ι →ₗ[R] V R ι where
  toFun x := (T a : LaurentPolynomial R) • x
  map_add' := smul_add _
  map_smul' := fun _ _ => smul_comm _ _ _
@[expose] def negativeUnit (n : ℕ) : (ι →₀ Polynomial R) →ₗ[R] V R ι :=
  (vectorShift R ι (-(n : ℤ))).comp (reciprocalUnit R ι)

lemma unitMap_single (f : Polynomial R →+* LaurentPolynomial R) (hC) (i : ι) (p : Polynomial R) :
    unitMap R ι f hC (Finsupp.single i p) = Pi.single i (f p) := by
  change coordinates R ι (FreeKernelCoefficientMap318.unit R f (Finsupp.single i p)) = _
  rw [unit_single]
  ext j
  simp [coordinates,Pi.single_apply,Finsupp.single_apply]

lemma positive_single (i : ι) (m : ℕ) (r : R) :
    positiveUnit R ι (Finsupp.single i (Polynomial.monomial m r)) = r • monomial i (m : ℤ) := by
  rw [positiveUnit,unitMap_single,Polynomial.toLaurent_C_mul_T]
  ext j
  by_cases h : j = i <;> simp [monomial,Pi.single_apply,h,eq_comm,LaurentPolynomial.smul_eq_C_mul]

lemma reciprocal_single (i : ι) (m : ℕ) (r : R) :
    reciprocalUnit R ι (Finsupp.single i (Polynomial.monomial m r)) = r • monomial i (-(m : ℤ)) := by
  rw [reciprocalUnit,unitMap_single,RingHom.comp_apply,Polynomial.toLaurent_C_mul_T,
    map_mul,invert_C,invert_T]
  ext j
  by_cases h : j = i <;> simp [monomial,Pi.single_apply,h,eq_comm,LaurentPolynomial.smul_eq_C_mul]

lemma positive_mem (x : ι →₀ Polynomial R) : positiveUnit R ι x ∈ (positive : Submodule R (V R ι)) := by
  refine x.induction_linear ?_ ?_ ?_
  · simpa only [map_zero] using (positive : Submodule R (V R ι)).zero_mem
  · intro x y hx hy
    simpa only [map_add] using (positive : Submodule R (V R ι)).add_mem hx hy
  · intro i p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Finsupp.single_add,map_add] using
        (positive : Submodule R (V R ι)).add_mem hp hq
    | monomial m r =>
      rw [positive_single]
      exact (positive : Submodule R (V R ι)).smul_mem r (monomial_mem i m (by simp))

lemma reciprocal_mem (x : ι →₀ Polynomial R) : reciprocalUnit R ι x ∈ (negative : Submodule R (V R ι)) := by
  refine x.induction_linear ?_ ?_ ?_
  · simpa only [map_zero] using (negative : Submodule R (V R ι)).zero_mem
  · intro x y hx hy
    simpa only [map_add] using (negative : Submodule R (V R ι)).add_mem hx hy
  · intro i p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Finsupp.single_add,map_add] using
        (negative : Submodule R (V R ι)).add_mem hp hq
    | monomial m r =>
      rw [reciprocal_single]
      exact (negative : Submodule R (V R ι)).smul_mem r (monomial_mem i (-(m : ℤ)) (by simp))

lemma negative_mem (n : ℕ) (x : ι →₀ Polynomial R) :
    negativeUnit R ι n x ∈ (upper (-(n : ℤ)) : Submodule R (V R ι)) := by
  exact shift_supported (-(n : ℤ)) (fun a ha => by
    change a ≤ 0 at ha
    change -(n : ℤ)+a ≤ -(n : ℤ)
    omega) (reciprocal_mem R ι x)
lemma positive_range : (positiveUnit R ι).range = (positive : Submodule R (V R ι)) := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact positive_mem R ι x
  · apply Submodule.span_le.mpr
    rintro y ⟨i,a,ha,rfl⟩
    change 0 ≤ a at ha
    refine ⟨Finsupp.single i (Polynomial.monomial a.toNat (1 : R)),?_⟩
    rw [positive_single,one_smul,Int.toNat_of_nonneg ha]

lemma negative_range (n : ℕ) :
    (negativeUnit R ι n).range = (upper (-(n : ℤ)) : Submodule R (V R ι)) := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact negative_mem R ι n x
  · apply Submodule.span_le.mpr
    rintro y ⟨i,a,ha,rfl⟩
    change a ≤ -(n : ℤ) at ha
    have hm : 0 ≤ -(n : ℤ)-a := by omega
    refine ⟨Finsupp.single i (Polynomial.monomial (-(n : ℤ)-a).toNat (1 : R)),?_⟩
    change (T (-(n : ℤ)) : LaurentPolynomial R) •
      reciprocalUnit R ι (Finsupp.single i (Polynomial.monomial (-(n : ℤ)-a).toNat (1 : R))) = _
    rw [reciprocal_single,one_smul,Int.toNat_of_nonneg hm,monomial_shift]
    congr 1
    omega
end FreeLaurentPolynomialUnits318
