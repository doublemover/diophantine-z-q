module
public import RelativeOriginalLaurentAlgebra318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace RelativePolynomialLaurentPushout318
open LaurentPolynomial
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R B : Type) [CommRing R] [CommRing B]
  [Algebra ℚ R] [Algebra ℚ B] [Algebra (Polynomial ℚ) B]
  [IsScalarTower ℚ (Polynomial ℚ) B]
attribute [local instance] Polynomial.algebra

local instance : Algebra (Polynomial ℚ) (LaurentPolynomial R) :=
  ((algebraMap (Polynomial R) (LaurentPolynomial R)).comp
    (algebraMap (Polynomial ℚ) (Polynomial R))).toAlgebra
local instance : IsScalarTower (Polynomial ℚ) (Polynomial R) (LaurentPolynomial R) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℚ (Polynomial ℚ) (LaurentPolynomial R) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower (Polynomial ℚ) (LaurentPolynomial ℚ) (LaurentPolynomial R) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a <;> simp [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.algebraMap_def,
    AddMonoidAlgebra.algebraMap_def,LaurentPolynomial.C,LaurentPolynomial.T]
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ)
    (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- Both actual coefficient pushouts reduce to the SAME Laurent
extension of the original rational polynomial chart. -/
@[expose] def finiteToCommon :
    LaurentPolynomial R ⊗[Polynomial R] (R ⊗[ℚ] B) ≃ₐ[LaurentPolynomial R]
      LaurentPolynomial R ⊗[Polynomial ℚ] B :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : LaurentPolynomial R ≃ₐ[LaurentPolynomial R] _)
    (RelativeOriginalPolynomialAlgebra318.polynomialComparison ℚ R B).symm).trans
      (Algebra.TensorProduct.cancelBaseChange (Polynomial ℚ) (Polynomial R)
        (LaurentPolynomial R) (LaurentPolynomial R) B)

@[expose] def commonToOverlap :
    LaurentPolynomial R ⊗[Polynomial ℚ] B ≃ₐ[LaurentPolynomial R]
      R ⊗[ℚ] (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B) :=
  (Algebra.TensorProduct.cancelBaseChange (Polynomial ℚ) (LaurentPolynomial ℚ)
    (LaurentPolynomial R) (LaurentPolynomial R) B).symm.trans
  (RelativeOriginalLaurentAlgebra318.laurentComparison ℚ R
    (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B))

/-- Literal ring pushout for the finite relative chart and its whole
Laurent localization, with no freeness choice and no pointwise argument. -/
@[expose] def equivalence :
    LaurentPolynomial R ⊗[Polynomial R] (R ⊗[ℚ] B) ≃ₐ[LaurentPolynomial R]
      R ⊗[ℚ] (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B) :=
  (finiteToCommon R B).trans (commonToOverlap R B)

lemma polynomialInverse_unit (b : B) :
    (RelativeOriginalPolynomialAlgebra318.polynomialComparison ℚ R B).symm ((1 : R) ⊗ₜ[ℚ] b) =
      (1 : Polynomial R) ⊗ₜ[Polynomial ℚ] b := by
  apply (RelativeOriginalPolynomialAlgebra318.polynomialComparison ℚ R B).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (RelativeOriginalPolynomialAlgebra318.comparison_unit ℚ R B b).symm

lemma equivalence_unit (b : B) :
    equivalence R B ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] ((1 : R) ⊗ₜ[ℚ] b)) =
      (1 : R) ⊗ₜ[ℚ] ((1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b) := by
  simp only [equivalence,finiteToCommon,commonToOverlap,AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,AlgEquiv.refl_apply,
    polynomialInverse_unit,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  exact RelativeOriginalLaurentAlgebra318.comparison_unit ℚ R _ _

@[expose] def rightMap : R ⊗[ℚ] B →ₐ[ℚ]
    R ⊗[ℚ] (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B) :=
  Algebra.TensorProduct.map (AlgHom.id ℚ R)
    ((Algebra.TensorProduct.includeRight (R := Polynomial ℚ)
      (A := LaurentPolynomial ℚ) (B := B)).restrictScalars ℚ)

/-- The ring pushout preserves the ENTIRE original finite-chart arrow,
not only its distinguished coordinate or its rational scalar subring. -/
lemma equivalence_right (t : R ⊗[ℚ] B) :
    equivalence R B ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] t) = rightMap R B t := by
  induction t using TensorProduct.inductionOn with
  | tmul r b =>
    have hs : (Polynomial.C r : Polynomial R) • ((1 : R) ⊗ₜ[ℚ] b) = r ⊗ₜ[ℚ] b := by
      change RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R B (Polynomial.C r) *
        ((1 : R) ⊗ₜ[ℚ] b) = _
      rw [RelativeOriginalPolynomialAlgebra318.polynomialMap_C,
        Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    have ht := TensorProduct.smul_tmul (Polynomial.C r) (1 : LaurentPolynomial R)
      ((1 : R) ⊗ₜ[ℚ] b)
    rw [hs] at ht
    have hc : (Polynomial.C r : Polynomial R) • (1 : LaurentPolynomial R) = C r := by
      simp only [Algebra.smul_def,LaurentPolynomial.algebraMap_eq_toLaurent,
        Polynomial.toLaurent_C,mul_one]
    rw [hc] at ht
    have he : (1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] (r ⊗ₜ[ℚ] b) =
        (C r : LaurentPolynomial R) •
          ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] ((1 : R) ⊗ₜ[ℚ] b)) := by
      simpa only [smul_tmul',smul_eq_mul,mul_one] using ht.symm
    rw [he,(equivalence R B).map_smul,equivalence_unit]
    change RelativeOriginalLaurentAlgebra318.laurentMap ℚ R
      (LaurentPolynomial ℚ ⊗[Polynomial ℚ] B) (C r) *
        ((1 : R) ⊗ₜ[ℚ] ((1 : LaurentPolynomial ℚ) ⊗ₜ[Polynomial ℚ] b)) = _
    rw [RelativeOriginalLaurentAlgebra318.laurentMap_C]
    simp only [rightMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
      AlgHom.restrictScalars_apply,Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add x y hx hy => simp only [tmul_add,map_add,hx,hy]
end RelativePolynomialLaurentPushout318
