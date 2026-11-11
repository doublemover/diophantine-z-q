module
public import OriginalFreePresentationBaseChange318
public import RelativeLaurentScalar318
public section
noncomputable section
namespace FreeKernelCoefficientMap318
open scoped TensorProduct
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (R : Type u) [CommRing R] {ι : Type v}
  (f : Polynomial R →+* LaurentPolynomial R)
local instance : Algebra (Polynomial R) (LaurentPolynomial R) := f.toAlgebra
variable (P : Submodule (Polynomial R) (ι →₀ Polynomial R))
  (K : Submodule (LaurentPolynomial R) (ι →₀ LaurentPolynomial R))
local instance : Module R P := Module.compHom P Polynomial.C
local instance : Module R K := RelativeLaurentScalar318.coefficientModule R K

@[expose] def unit (x : ι →₀ Polynomial R) : ι →₀ LaurentPolynomial R :=
  OriginalFreePresentationBaseChange318.freeEquivalence (Polynomial R) (LaurentPolynomial R)
    ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)

lemma unit_add (x y : ι →₀ Polynomial R) : unit R f (x+y) = unit R f x + unit R f y := by
  unfold unit
  rw [TensorProduct.tmul_add,map_add]

lemma unit_smul (p : Polynomial R) (x : ι →₀ Polynomial R) :
    unit R f (p • x) = f p • unit R f x := by
  let e := OriginalFreePresentationBaseChange318.freeEquivalence (Polynomial R) (LaurentPolynomial R)
  change e ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] (p • x)) =
    f p • e ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)
  rw [← e.map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  have h := TensorProduct.smul_tmul p (1 : LaurentPolynomial R) x
  apply congrArg e
  simpa only [Algebra.smul_def,mul_one] using h.symm

variable (κ : P → K) (hκ : ∀ x : P, (κ x : ι →₀ LaurentPolynomial R) = unit R f x)

include hκ in
lemma additive (x y : P) : κ (x+y) = κ x + κ y := by
  apply Subtype.ext
  change (κ (x+y) : ι →₀ LaurentPolynomial R) = (κ x : ι →₀ LaurentPolynomial R) + κ y
  rw [hκ,hκ,hκ]
  exact unit_add R f x y

include hκ in
lemma polynomial (p : Polynomial R) (x : P) : κ (p • x) = f p • κ x := by
  apply Subtype.ext
  change (κ (p • x) : ι →₀ LaurentPolynomial R) = f p • (κ x : ι →₀ LaurentPolynomial R)
  rw [hκ,hκ]
  exact unit_smul R f p x

/-- Coefficient linearity of the ORIGINAL relation-unit map follows from
its actual free-source coordinates, not an assumed kernel comparison. -/
@[expose] def map (hC : ∀ r : R, f (Polynomial.C r) = LaurentPolynomial.C r) : P →ₗ[R] K where
  toFun := κ
  map_add' := additive R f P K κ hκ
  map_smul' r x := by
    change κ ((Polynomial.C r) • x) = (LaurentPolynomial.C r : LaurentPolynomial R) • κ x
    rw [polynomial R f P K κ hκ,hC]
end FreeKernelCoefficientMap318
