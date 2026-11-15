module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

public section
noncomputable section
namespace GeometricIntegralConstants318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- A geometrically integral algebra has no new algebraic constants. The
domain hypothesis is on the actual scalar extension, not an abstract model. -/
theorem integral_is_constant
    [IsDomain (AlgebraicClosure K ⊗[K] A)] {x : A} (hx : IsIntegral K x) :
    ∃ a : K, algebraMap K A a = x := by
  let F := AlgebraicClosure K
  let T := F ⊗[K] A
  let y : T := Algebra.TensorProduct.includeRight x
  have hy : IsIntegral F y :=
    (hx.map (Algebra.TensorProduct.includeRight : A →ₐ[K] T)).tower_top
  let z : integralClosure F T := ⟨y, hy⟩
  obtain ⟨a, ha⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := integralClosure F T)).surjective z
  have he : a ⊗ₜ[K] (1 : A) = (1 : F) ⊗ₜ[K] x :=
    congrArg Subtype.val ha
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : F) ≠ 0)
  let g : T →ₗ[K] A := TensorProduct.lift ((LinearMap.lsmul K A).comp f)
  refine ⟨f a, ?_⟩
  have hg := congrArg g he
  dsimp only [g] at hg
  rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul] at hg
  simpa only [g, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearMap.lsmul_apply, hf, one_smul,
    Algebra.smul_def, mul_one, map_one, one_mul] using hg

end GeometricIntegralConstants318
