module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Span.Defs
public section
noncomputable section
namespace ScalarRestrictionOriginalSpan318
open CategoryTheory
open scoped ChangeOfRings
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra C B] (f : A →+* B) (N : ModuleCat.{u} A) (M : ModuleCat.{u} B)
  [Module C M] [IsScalarTower C B M]
  (e : (ModuleCat.extendScalars f).obj N ≅ M) (ρ : N → M)
  (hρ : ∀ n : N, e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N n) = ρ n)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

include hρ in
lemma original_smul (a : A) (n : N) : ρ (a • n) = f a • ρ n := by
  let q : N →ₛₗ[f] M := (ModuleCat.semilinearMapAddEquiv f N M).symm
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app N ≫
      (ModuleCat.restrictScalars f).map e.hom)
  have hq : ∀ m : N, q m = ρ m := by
    intro m
    exact hρ m
  rw [← hq, ← hq]
  exact q.map_smulₛₗ a n

include hρ in
/-- If the actual chart ring generates its actual overlap ring over the
coordinate ring, the actual restriction of every original affine module
generates its whole overlap module over that SAME coordinate ring.
This is genuine tensor/span induction, not a finite-free assumption. -/
theorem original_span
    (hB : Submodule.span C (Set.range f) = ⊤) :
    Submodule.span C (Set.range ρ) = ⊤ := by
  let P := Submodule.span C (Set.range ρ)
  have hs (b : B) (n : N) : b • ρ n ∈ P := by
    have hb : b ∈ Submodule.span C (Set.range f) := by rw [hB]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨a,rfl⟩
      rw [← original_smul f N M e ρ hρ]
      exact Submodule.subset_span ⟨a • n,rfl⟩
    · simpa only [zero_smul] using P.zero_mem
    · intro x y _ _ hx hy
      simpa only [add_smul] using P.add_mem hx hy
    · intro c x _ hx
      simpa only [smul_assoc] using P.smul_mem c hx
  have he (x : (ModuleCat.extendScalars f).obj N) : e.hom x ∈ P := by
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
        have ht : (b ⊗ₜ[A,f] n : (ModuleCat.extendScalars f).obj N) =
            (show B from b) • ((1 : B) ⊗ₜ[A,f] n) := by
          rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
        rw [ht,map_smul]
        change (show B from b) • e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N n) ∈ P
        rw [hρ]
        exact hs (show B from b) n
    | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  apply top_unique
  intro x _
  obtain ⟨y,rfl⟩ := e.toLinearEquiv.surjective x
  exact he y
end ScalarRestrictionOriginalSpan318
