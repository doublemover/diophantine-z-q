module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Span.Defs
public section
noncomputable section
namespace ScalarExtensionOriginalSpan318
open CategoryTheory
open scoped ChangeOfRings
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (f : A →+* B) (N : ModuleCat.{u} A) (M : ModuleCat.{u} B)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unit with its EXTENDED carrier made explicit before span
inference; the restricted carrier has no intended B-module instance. -/
@[expose] def unit : N → (ModuleCat.extendScalars f).obj N :=
  fun n => (1 : B) ⊗ₜ[A,f] n

lemma unit_actual (n : N) : unit f N n =
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app N n : (ModuleCat.extendScalars f).obj N) := rfl

/-- The original unit spans the entire extended B-module. -/
lemma unit_span : Submodule.span B (Set.range (unit f N)) = ⊤ := by
  let P : Submodule B ((ModuleCat.extendScalars f).obj N) := Submodule.span B (Set.range (unit f N))
  apply top_unique
  intro x _
  change x ∈ P
  induction x using TensorProduct.inductionOn with
  | tmul b n =>
      have ht : (b ⊗ₜ[A,f] n : (ModuleCat.extendScalars f).obj N) = b • unit f N n := by
        change b ⊗ₜ[A,f] n = b • ((1 : B) ⊗ₜ[A,f] n)
        rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
      rw [ht]
      exact P.smul_mem b (Submodule.subset_span ⟨n,rfl⟩)
  | add x y hx hy => exact P.add_mem hx hy

/-- A comparison with the actual unit proves that the original chart
restriction spans. Direct tensor induction avoids an ambiguous span
induction motive over the restricted-versus-extended carrier. -/
lemma original_span (e : (ModuleCat.extendScalars f).obj N ≅ M)
    (ρ : N → M)
    (hρ : ∀ x : N, e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x) = ρ x) :
    Submodule.span B (Set.range ρ) = ⊤ := by
  let P : Submodule B M := Submodule.span B (Set.range ρ)
  have hu (x : (ModuleCat.extendScalars f).obj N) : e.hom x ∈ P := by
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
        have ht : (b ⊗ₜ[A,f] n : (ModuleCat.extendScalars f).obj N) = b • unit f N n := by
          change b ⊗ₜ[A,f] n = b • ((1 : B) ⊗ₜ[A,f] n)
          rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
        rw [ht,map_smul,unit_actual,hρ]
        exact P.smul_mem b (Submodule.subset_span ⟨n,rfl⟩)
    | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  apply top_unique
  intro x _
  obtain ⟨y,rfl⟩ := e.toLinearEquiv.surjective x
  exact hu y
end ScalarExtensionOriginalSpan318
