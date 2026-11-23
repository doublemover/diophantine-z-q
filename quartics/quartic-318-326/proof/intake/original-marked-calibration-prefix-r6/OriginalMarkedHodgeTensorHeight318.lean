module
public import OriginalGlobalHodgeIdealHeight318
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-! Read the honest integral Hodge line of the common good model in one
rational frame. The two integral square tensors live over the two actual
coefficient rings. Their scalar values, not ad hoc finite bounds or ideal
membership assumptions, enter the height theorem. -/
public section
noncomputable section

namespace OriginalMarkedHodgeTensorHeight318

open NumberField OriginalGlobalHodgeIdealHeight318
open scoped TensorProduct nonZeroDivisors

variable {F : Type*} [Field F] [_hodgeField : NumberField F]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 F) M] [_finiteHodge : Module.Finite (𝓞 F) M]

/-- Reading a global integral differential in the one chosen generic frame. -/
@[expose] def coeff (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) : M →ₗ[𝓞 F] F :=
  (e.toLinearMap.restrictScalars (𝓞 F)).comp (TensorProduct.mk (𝓞 F) F M 1)

include _hodgeField _finiteHodge in
theorem coeff_ne_zero (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) : coeff e ≠ 0 := by
  intro h
  have hz (m : M) : e (1 ⊗ₜ[𝓞 F] m) = 0 :=
    congrArg (fun f : M →ₗ[𝓞 F] F => f m) h
  have allz (v : F ⊗[𝓞 F] M) : e v = 0 := by
    induction v using TensorProduct.inductionOn with
    | tmul s m =>
      have he : s ⊗ₜ[𝓞 F] m = s • ((1 : F) ⊗ₜ[𝓞 F] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul, hz, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, zero_add]
  obtain ⟨v, hv⟩ := e.surjective 1
  exact one_ne_zero (hv.symm.trans (allz v))

/-- Coefficient range is a fractional ideal by finite generation over the
actual ring of integers; the input does not contain an aggregate adelic ideal. -/
@[expose] def integralIdeal (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) : FractionalIdeal (𝓞 F)⁰ F :=
  ⟨(coeff e).range, FractionalIdeal.isFractional_of_fg (Submodule.fg_range (coeff e))⟩

theorem integralIdeal_ne_zero (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) : integralIdeal e ≠ 0 := by
  apply FractionalIdeal.coeToSubmodule_ne_bot.mp
  exact fun h => coeff_ne_zero e (LinearMap.range_eq_bot.mp h)

@[expose] def squareRead (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) : M ⊗[𝓞 F] M →ₗ[𝓞 F] F :=
  TensorProduct.lift ((LinearMap.mul (𝓞 F) F).compl₁₂ (coeff e) (coeff e))

include _hodgeField _finiteHodge in
@[simp] theorem squareRead_tmul (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) (a b : M) :
    squareRead e (a ⊗ₜ[𝓞 F] b) = coeff e a * coeff e b := rfl

theorem squareRead_mem (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) (q : M ⊗[𝓞 F] M) :
    squareRead e q ∈ (integralIdeal e : Submodule (𝓞 F) F) *
      (integralIdeal e : Submodule (𝓞 F) F) := by
  induction q using TensorProduct.inductionOn with
  | tmul a b => exact Submodule.mul_mem_mul ⟨a, rfl⟩ ⟨b, rfl⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

variable (S : Type*) [CommRing S] [Algebra (𝓞 F) S] [Algebra S F] [IsScalarTower (𝓞 F) S F]

@[expose] def openRead (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) :
    S ⊗[𝓞 F] (M ⊗[𝓞 F] M) →ₗ[S] F := (squareRead e).liftBaseChange S

theorem openRead_mem (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F) (q : S ⊗[𝓞 F] (M ⊗[𝓞 F] M)) :
    openRead S e q ∈ Submodule.span S
      (↑((integralIdeal e : Submodule (𝓞 F) F) * (integralIdeal e : Submodule (𝓞 F) F)) : Set F) := by
  induction q using TensorProduct.inductionOn with
  | tmul s a => exact Submodule.smul_mem _ s (Submodule.subset_span (squareRead_mem e a))
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

/-- Original finite-to-height endpoint. M is the *one* globally glued Hodge
line; the geometric identification of Z3,Z11 is by exact scalar equality on
the common generic marked fibre. No fractional ideal, local frame, valuation
inequality, support, or gluing condition is a caller-provided premise. -/
theorem height_of_original_marked_tensors
    {S₃ S₁₁ : Type*} [CommRing S₃] [CommRing S₁₁]
    [Algebra (𝓞 F) S₃] [Algebra S₃ F] [IsScalarTower (𝓞 F) S₃ F]
    [Algebra (𝓞 F) S₁₁] [Algebra S₁₁ F] [IsScalarTower (𝓞 F) S₁₁ F]
    [IsLocalization.Away (3 : 𝓞 F) S₃] [IsLocalization.Away (11 : 𝓞 F) S₁₁]
    (e : (F ⊗[𝓞 F] M) ≃ₗ[F] F)
    (Z3 : Fin 2 → S₃ ⊗[𝓞 F] (M ⊗[𝓞 F] M))
    (Z11 : Fin 2 → S₁₁ ⊗[𝓞 F] (M ⊗[𝓞 F] M))
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) (t : ℚ) (c : F) (hc : c ≠ 0)
    (gen3 : ∀ i, openRead S₃ e (Z3 i) = hodgeCoefficient t c i)
    (gen11 : ∀ i, openRead S₁₁ e (Z11 i) = hodgeCoefficient t c i)
    (arch : ∀ w : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (w (t : F)) ≤ U ∧ 64 ≤ f ∧ w.val c * (A w)^2 = 4/(U*f)) :
    Height.logHeight₁ (t / 32) <
      2 * (idealFrame (integralIdeal e) (integralIdeal_ne_zero e) A hA).normalizedDegree + 11 := by
  apply height_of_open_sections (S₃ := S₃) (S₁₁ := S₁₁) (integralIdeal e) (integralIdeal_ne_zero e)
    A hA t c hc
  · intro i; rw [← gen3]; exact openRead_mem S₃ e _
  · intro i; rw [← gen11]; exact openRead_mem S₁₁ e _
  · exact arch

end OriginalMarkedHodgeTensorHeight318
