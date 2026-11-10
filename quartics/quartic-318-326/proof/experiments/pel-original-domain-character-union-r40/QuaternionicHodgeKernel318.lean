module
public import QuaternionicRealPeriod318
public section
noncomputable section
namespace QuaternionicHodgeKernel318
set_option maxHeartbeats 700000
abbrev Matrices := Matrix (Fin 2) (Fin 2) ℂ
abbrev Vectors := Fin 2 → ℂ

/-- Complexification of M↦M(τ,1), with its exact kernel rather than a
freely supplied abstract rank-two Hodge space. -/
@[expose] def projection (τ : ℂ) : Matrices →ₗ[ℂ] Vectors where
  toFun M i := M i 0*τ+M i 1
  map_add' M N := by
    funext i
    change (M i 0+N i 0)*τ+(M i 1+N i 1)=(M i 0*τ+M i 1)+(N i 0*τ+N i 1)
    ring
  map_smul' a M := by
    funext i
    change (a*M i 0)*τ+a*M i 1=a*(M i 0*τ+M i 1)
    ring

@[expose] def inclusion (τ : ℂ) : Vectors →ₗ[ℂ] Matrices where
  toFun z i := ![z i,-z i*τ]
  map_add' z w := by
    funext i j
    fin_cases j
    · change z i+w i=z i+w i
      rfl
    · change -(z i+w i)*τ=(-z i*τ)+(-w i*τ)
      ring
  map_smul' a z := by
    funext i j
    fin_cases j
    · change a*z i=a*z i
      rfl
    · change -(a*z i)*τ=a*(-z i*τ)
      ring

@[expose] def splitting : Vectors →ₗ[ℂ] Matrices where
  toFun z i := ![0,z i]
  map_add' z w := by
    funext i j
    fin_cases j
    · change (0:ℂ)=0+0
      ring
    · change z i+w i=z i+w i
      rfl
  map_smul' a z := by
    funext i j
    fin_cases j
    · change (0:ℂ)=a*0
      ring
    · change a*z i=a*z i
      rfl

@[expose] def Hodge (τ : ℂ) : Submodule ℂ Matrices := (projection τ).ker

theorem projection_inclusion (τ : ℂ) (z : Vectors) : projection τ (inclusion τ z)=0 := by
  funext i
  change z i*τ+(-z i*τ)=0
  ring

theorem projection_splitting (τ : ℂ) (z : Vectors) : projection τ (splitting z)=z := by
  funext i
  change 0*τ+z i=z i
  ring

theorem decomposition (τ : ℂ) (M : Matrices) :
    inclusion τ (fun i => M i 0)+splitting (projection τ M)=M := by
  funext i j
  fin_cases j
  · change M i 0+0=M i 0
    ring
  · change -M i 0*τ+(M i 0*τ+M i 1)=M i 1
    ring

@[expose] def frame (τ : ℂ) : Vectors ≃ₗ[ℂ] Hodge τ where
  toFun z := ⟨inclusion τ z,projection_inclusion τ z⟩
  invFun M i := M.val i 0
  left_inv z := by funext i; rfl
  right_inv M := by
    apply Subtype.ext
    have h := decomposition τ M.val
    have hz : projection τ M.val=0 := M.property
    simpa only [hz,map_zero,add_zero] using h
  map_add' z w := by apply Subtype.ext; exact (inclusion τ).map_add z w
  map_smul' a z := by apply Subtype.ext; exact (inclusion τ).map_smul a z

@[expose] def leftAction (g : Matrices) (z : Vectors) : Vectors :=
  fun i => g i 0*z 0+g i 1*z 1

theorem projection_left_mul (τ : ℂ) (g M : Matrices) :
    projection τ (g*M)=leftAction g (projection τ M) := by
  funext i
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_apply,Fin.sum_univ_two,leftAction]
  ring

theorem inclusion_left_mul (τ : ℂ) (g : Matrices) (z : Vectors) :
    g*inclusion τ z=inclusion τ (leftAction g z) := by
  funext i j
  fin_cases j <;> simp only [Matrix.mul_apply,Fin.sum_univ_two]
  · change g i 0*z 0+g i 1*z 1=g i 0*z 0+g i 1*z 1
    rfl
  · change g i 0*(-z 0*τ)+g i 1*(-z 1*τ)=-(g i 0*z 0+g i 1*z 1)*τ
    ring

/-- The entire kernel is invariant under every specified left matrix action;
there is no choice of a different Hodge subspace for different elements. -/
theorem hodge_stable (τ : ℂ) (g : Matrices) (M : Hodge τ) : g*M.val∈Hodge τ := by
  change projection τ (g*M.val)=0
  rw [projection_left_mul,show projection τ M.val=0 from M.property]
  funext i
  simp only [leftAction,Pi.zero_apply,mul_zero,add_zero]
end QuaternionicHodgeKernel318
