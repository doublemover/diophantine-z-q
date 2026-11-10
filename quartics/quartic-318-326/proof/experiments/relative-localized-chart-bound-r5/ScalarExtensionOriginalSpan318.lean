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

/-- The original scalar-extension unit generates the entire extended module.
This is tensor induction, valid without flatness, reducedness or freeness. -/
lemma unit_span :
    Submodule.span B (Set.range (fun x : N =>
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x :
        (ModuleCat.extendScalars f).obj N))) = ⊤ := by
  let P := Submodule.span B (Set.range (fun x : N =>
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x :
      (ModuleCat.extendScalars f).obj N)))
  apply top_unique
  intro x _
  change x ∈ P
  induction x using TensorProduct.inductionOn with
  | tmul b n =>
      have h : (b ⊗ₜ[A,f] n : (ModuleCat.extendScalars f).obj N) =
          b • ((1 : B) ⊗ₜ[A,f] n) := by
        rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
      rw [h]
      exact P.smul_mem b (Submodule.subset_span ⟨n,rfl⟩)
  | add x y hx hy => exact P.add_mem hx hy

/-- A comparison with the ACTUAL scalar-extension unit proves that the
original chart restriction spans the entire overlap module. -/
lemma original_span (e : (ModuleCat.extendScalars f).obj N ≅ M)
    (ρ : N → M)
    (hρ : ∀ x : N, e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N x) = ρ x) :
    Submodule.span B (Set.range ρ) = ⊤ := by
  let P := Submodule.span B (Set.range ρ)
  have hu : ∀ x : (ModuleCat.extendScalars f).obj N, e.hom x ∈ P := by
    intro x
    have hx : x ∈ Submodule.span B (Set.range (fun n : N =>
        ((ModuleCat.extendRestrictScalarsAdj f).unit.app N n :
          (ModuleCat.extendScalars f).obj N))) := by
      rw [unit_span f N]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨n,rfl⟩
      rw [hρ]
      exact Submodule.subset_span ⟨n,rfl⟩
    · simpa only [map_zero] using P.zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using P.add_mem hx hy
    · intro b x _ hx
      simpa only [map_smul] using P.smul_mem b hx
  apply top_unique
  intro x _
  obtain ⟨y,rfl⟩ := e.toLinearEquiv.surjective x
  exact hu y
end ScalarExtensionOriginalSpan318
