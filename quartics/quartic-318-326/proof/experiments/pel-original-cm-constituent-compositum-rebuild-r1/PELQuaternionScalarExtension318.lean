module
public import PELActualUnramifiedSplitting318
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace PELQuaternionScalarExtension318
open PELQuaternionAlgebra318 QuaternionAlgebra
open scoped TensorProduct
set_option maxHeartbeats 1600000
universe u
variable (F : Type u) [Field F] [CharZero F]
abbrev Presentation := QuaternionAlgebra F (-210) 0 5
abbrev Extension := F ⊗[ℚ] B

/-- The canonical coefficient map from the ORIGINAL rational quaternion
algebra to its same-parameter presentation over F. -/
@[expose] def coefficients : B →ₐ[ℚ] Presentation F where
  toFun x := ⟨(x.re:F),(x.imI:F),(x.imJ:F),(x.imK:F)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> push_cast <;> norm_num <;> ring
  commutes' q := by
    change (⟨(q:F),0,0,0⟩ : Presentation F)=_
    rfl

/-- This is the genuine tensor-product universal map over F. -/
@[expose] def forward : Extension F →ₐ[F] Presentation F :=
  AlgHom.liftEquiv ℚ F B (Presentation F) (coefficients F)

theorem forward_tmul (a : F) (q : B) :
    forward F (a ⊗ₜ[ℚ] q)=a • coefficients F q :=
  AlgHom.liftEquiv_tmul (coefficients F) a q

@[expose] def right : B →ₐ[ℚ] Extension F := Algebra.TensorProduct.includeRight

theorem forward_right (q : B) : forward F (right F q)=coefficients F q := by
  change forward F (1 ⊗ₜ[ℚ] q)=_
  rw [forward_tmul,one_smul]

/-- The same original i,j,k inside the ACTUAL scalar extension satisfy the
quaternion relations over F; none is replaced by a chosen abstract basis. -/
@[expose] def tensorBasis : QuaternionAlgebra.Basis (Extension F) (-210:F) 0 5 where
  i := right F mu
  j := right F j
  k := right F k
  i_mul_i := by
    rw [←map_mul,mu_square]
    simp [Algebra.smul_def]
  j_mul_j := by
    rw [←map_mul,j_square]
    simp [Algebra.smul_def]
  i_mul_j := by rw [←map_mul,mu_j]
  j_mul_i := by rw [←map_mul,j_mu,map_neg,zero_smul,zero_sub]

@[expose] def backward : Presentation F →ₐ[F] Extension F := (tensorBasis F).liftHom

theorem backward_i : backward F (⟨0,1,0,0⟩ : Presentation F)=right F mu := by
  simp [backward,QuaternionAlgebra.Basis.lift,tensorBasis]
theorem backward_j : backward F (⟨0,0,1,0⟩ : Presentation F)=right F j := by
  simp [backward,QuaternionAlgebra.Basis.lift,tensorBasis]

theorem forward_backward : (forward F).comp (backward F)=AlgHom.id F (Presentation F) := by
  apply QuaternionAlgebra.hom_ext
  · change forward F (backward F (⟨0,1,0,0⟩ : Presentation F))=⟨0,1,0,0⟩
    rw [backward_i,forward_right]
    ext <;> simp [coefficients,mu]
  · change forward F (backward F (⟨0,0,1,0⟩ : Presentation F))=⟨0,0,1,0⟩
    rw [backward_j,forward_right]
    ext <;> simp [coefficients,j]

theorem backward_forward : (backward F).comp (forward F)=AlgHom.id F (Extension F) := by
  apply Algebra.TensorProduct.ext_ring
  apply QuaternionAlgebra.hom_ext
  · change backward F (forward F (right F mu))=right F mu
    rw [forward_right]
    have h : coefficients F mu=(⟨0,1,0,0⟩ : Presentation F) := by ext <;> simp [coefficients,mu]
    rw [h,backward_i]
  · change backward F (forward F (right F j))=right F j
    rw [forward_right]
    have h : coefficients F j=(⟨0,0,1,0⟩ : Presentation F) := by ext <;> simp [coefficients,j]
    rw [h,backward_j]

/-- Exact scalar extension of the original rational quaternion algebra,
including both inverse laws and the F-algebra structure. -/
@[expose] def equivalence : Extension F ≃ₐ[F] Presentation F :=
  { forward F with
    invFun := backward F
    left_inv := fun x => DFunLike.congr_fun (backward_forward F) x
    right_inv := fun x => DFunLike.congr_fun (forward_backward F) x }

theorem equivalence_original (q : B) :
    equivalence F (1 ⊗ₜ[ℚ] q)=coefficients F q := forward_right F q

theorem equivalence_scalar (a : F) :
    equivalence F (algebraMap F (Extension F) a)=
      algebraMap F (Presentation F) a := (equivalence F).commutes a
end PELQuaternionScalarExtension318
