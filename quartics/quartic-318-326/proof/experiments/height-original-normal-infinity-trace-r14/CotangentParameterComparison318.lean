module
public import FramedCotangentFiber318
public section
noncomputable section
namespace CotangentParameterComparison318
open scoped TensorProduct
set_option maxHeartbeats 800000
variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]
  (e : U ≃ₗ[K] K) (f : W ≃ₗ[K] K) (p : U) (q : W)
  (hp : e p≠0) (hq : f q≠0)

/-- Canonical comparison of two one-dimensional cotangent fibers carrying
the same original parameter differential. The scalar is forced by Dt. -/
@[expose] def comparison : U ≃ₗ[K] W :=
  e ≪≫ₗ LinearEquiv.smulOfUnit (M:=K) (Units.mk0 (f q/e p) (div_ne_zero hq hp)) ≪≫ₗ f.symm

theorem comparison_value (x : U) :
    f (comparison e f p q hp hq x)=(f q/e p)*e x := by
  change f (f.symm ((f q/e p)*e x))=_
  exact f.apply_symm_apply _

theorem comparison_parameter : comparison e f p q hp hq p=q := by
  apply f.injective
  rw [comparison_value,div_mul_cancel₀ _ hp]

/-- The parameter condition determines the entire linear map, rather than
merely comparing the values of the two selected sections. -/
theorem unique (g : U →ₗ[K] W) (hg : g p=q) :
    g=(comparison e f p q hp hq).toLinearMap := by
  apply LinearMap.ext
  intro x
  have hx : x=(e x/e p) • p := by
    apply e.injective
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hp]
  rw [hx,map_smul,map_smul,hg,comparison_parameter]

@[expose] def squareComparison : (U ⊗[K] U) ≃ₗ[K] (W ⊗[K] W) :=
  TensorProduct.congr (comparison e f p q hp hq) (comparison e f p q hp hq)

theorem square_parameter :
    squareComparison e f p q hp hq (p ⊗ₜ[K] p)=q ⊗ₜ[K] q := by
  simp only [squareComparison,TensorProduct.congr_tmul,comparison_parameter]

/-- Exact quadratic frame transition, retaining the original derivative
normalizations on both actual cotangent fibers. -/
theorem square_coefficient (x : U) (hx : e x=1) :
    f (comparison e f p q hp hq x)^2=(f q/e p)^2 := by
  rw [comparison_value,hx,mul_one]

/-- The actual induced tensor-square map sends weighted normalized
coordinate squares by the square of the forced derivative ratio. -/
theorem square_weighted (x : U) (y : W) (hx : e x=1) (hy : f y=1) (a : K) :
    squareComparison e f p q hp hq (a • (x ⊗ₜ[K] x))=
      ((f q/e p)^2*a) • (y ⊗ₜ[K] y) := by
  have hxy : comparison e f p q hp hq x=(f q/e p) • y := by
    apply f.injective
    rw [comparison_value,hx,mul_one,map_smul,hy,smul_eq_mul,mul_one]
  rw [map_smul,squareComparison,TensorProduct.congr_tmul,hxy,
    TensorProduct.smul_tmul_smul,smul_smul]
  congr 1
  ring

include hp in
/-- The cleared bicanonical identities force the same quadratic transition
on coefficients. This is independent of the section-pair ratio argument. -/
theorem coefficient_transition (P J a b : K) (hP : P≠0)
    (ha : P*a=J^2*(e p)^2) (hb : P*b=J^2*(f q)^2) :
    b=(f q/e p)^2*a := by
  apply (mul_left_cancel₀ hP)
  calc
    P*b = J^2*(f q)^2 := hb
    _ = (f q/e p)^2*(J^2*(e p)^2) := by
      field_simp [hp]
      <;> ring
    _ = (f q/e p)^2*(P*a) := by rw [ha]
    _ = P*((f q/e p)^2*a) := by ring
end CotangentParameterComparison318
