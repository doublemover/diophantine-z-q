module
public import SelectedPrimitiveFixedX318
public import SelectedQuadraticAffineEqualizer318
public import Mathlib.RingTheory.Flat.Equalizer
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial EvenContactEtale318
open scoped TensorProduct
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318

namespace SelectedPrimitiveRootSignDescent318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q)

/-- The actual negation-fixed algebra, in the precise form needed by
the pinned flat equalizer theorem. -/
abbrev Fixed := AlgHom.equalizer τ (AlgHom.id R Q)

theorem fixed_eq : Fixed n I τ = SelectedPrimitiveFixedX318.fixed n I τ := by
  ext z
  rfl

variable (c : Rˣ)
local notation "U" => RootRing c

/-- Native exact flat base change of the ACTUAL two fixed equations,
using the proved free module structure of the same quadratic cover. -/
@[expose] def fixedBaseChange :
    U ⊗[R] Fixed n I τ ≃ₐ[U]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id U U) τ)
        (Algebra.TensorProduct.map (AlgHom.id U U) (AlgHom.id R Q)) := by
  letI : Module.Free R U := rootRing_free c
  exact AlgHom.tensorEqualizerEquiv U U τ (AlgHom.id R Q)

abbrev rootUnit : Uˣ := (root_isUnit c).unit

private theorem root_sq_unit :
    (rootUnit n c)^2 = Units.map (algebraMap R U).toMonoidHom c := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, (root_isUnit c).unit_spec]
  exact root_square c

/-- The inverse square is a BASE scalar, with the original orientation:
inverse transport sends x_V to r⁻²x_V=c⁻¹x_V. -/
theorem inverse_square :
    (↑((rootUnit n c)⁻¹):U)^2 = algebraMap R U (↑c⁻¹:R) := by
  have h : ((rootUnit n c)⁻¹)^2 = Units.map (algebraMap R U).toMonoidHom c⁻¹ := by
    rw [inv_pow,root_sq_unit, map_inv]
  simpa only [Units.val_pow_eq_pow_val] using congrArg (fun z : Uˣ => (z:U)) h

variable (hτ : τ.comp (q n I) = (q n I).comp (sign n))
variable (mark : Q →ₐ[R] U) (xV : R)
variable (hx : mark (xbar n I) = (↑((rootUnit n c)⁻¹):U)^2 * algebraMap R U xV)
local notation "s" => ((↑c⁻¹:R)*xV)
local notation "F" => Fixed n I τ

include hx in
theorem mark_x_scalar : mark (xbar n I) = algebraMap R U s := by
  rw [hx,inverse_square,map_mul]

/-- The inverse-literal mark, restricted to its actual fixed algebra. -/
@[expose] def invariantMark : F →ₐ[R] U := mark.comp F.val

include hτ hx in
private theorem invariant_value_scalar (z : F) :
    ∃ a : R, algebraMap R U a = invariantMark n I τ c mark z := by
  have hz : τ (z:Q) = (z:Q) := z.property
  obtain ⟨p,hp⟩ := (fixed_iff_polynomial n I τ hτ (z:Q)).mp hz
  have hh : mark.comp (aeval (xbar n I)) =
      (Algebra.ofId R U).comp (aeval s) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply,aeval_X] using mark_x_scalar n I c mark xV hx
  refine ⟨aeval s p,?_⟩
  have h := DFunLike.congr_fun hh p
  simpa only [AlgHom.comp_apply,hp,invariantMark] using h.symm

include hτ hx in
/-- The TWO actual tensor-product branch maps agree on all actual fixed
coordinates. This is an equality of algebra maps, not a test on points. -/
theorem branch_equalizer :
    (SelectedQuadraticAffineEqualizer318.left c).comp (invariantMark n I τ c mark) =
      (SelectedQuadraticAffineEqualizer318.right c).comp (invariantMark n I τ c mark) := by
  apply AlgHom.ext
  intro z
  obtain ⟨a,ha⟩ := invariant_value_scalar n I τ c hτ mark xV hx z
  change SelectedQuadraticAffineEqualizer318.left c (invariantMark n I τ c mark z) =
    SelectedQuadraticAffineEqualizer318.right c (invariantMark n I τ c mark z)
  rw [←ha]
  exact SelectedQuadraticAffineEqualizer318.scalar_equalizes c a

include hτ hx in
/-- Effective affine descent of this exact invariant evaluation across the
actual root cover. It descends the sign class, not the marked section. -/
theorem descends [Nontrivial R] :
    ∃! φ : F →ₐ[R] R, (Algebra.ofId R U).comp φ = invariantMark n I τ c mark :=
  SelectedQuadraticAffineEqualizer318.factor_unique c _ (branch_equalizer n I τ c hτ mark xV hx)

end SelectedPrimitiveRootSignDescent318

#print axioms SelectedPrimitiveRootSignDescent318.fixedBaseChange
#print axioms SelectedPrimitiveRootSignDescent318.branch_equalizer
#print axioms SelectedPrimitiveRootSignDescent318.descends
