module
public import OriginalAffineLinePathSections318
public section
noncomputable section
namespace OriginalAffineGeneratorPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct ChangeOfRings
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Generation over a smaller actual coordinate ring implies generation
over the original chart ring, with the scalar tower explicitly retained. -/
lemma span_of_restriction (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    (M : Type u) [AddCommGroup M] [Module C M] [Module A M] [IsScalarTower C A M]
    {ι : Type*} (g : ι → M) (hg : Submodule.span C (Set.range g)=⊤) :
    Submodule.span A (Set.range g)=⊤ := by
  apply top_unique
  intro x hx
  have h : x ∈ Submodule.span C (Set.range g) := by rw [hg]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro y hy; exact Submodule.subset_span hy
  · exact (Submodule.span A (Set.range g)).zero_mem
  · intro a b _ _ ha hb; exact (Submodule.span A (Set.range g)).add_mem ha hb
  · intro c x _ hx
    rw [← IsScalarTower.algebraMap_smul A c x]
    exact (Submodule.span A (Set.range g)).smul_mem _ hx

variable {A B : CommRingCat.{u}} (f : A ⟶ B) (L : Line (Spec A))
  (N : Line (Spec B)) (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  {ι : Type*} (g : ι → OriginalLineAffineModel318.sections A L)

/-- Actual global generators of an original affine line remain generators
under its genuine affine geometric pullback and specified line comparison.
This covers original principal frame neighborhoods, not just field points. -/
lemma span (hg : Submodule.span A (Set.range g)=⊤) :
    Submodule.span B (Set.range (fun i => OriginalAffineLinePathSections318.restriction f L N e (g i)))=⊤ := by
  let Q := Submodule.span B
    (Set.range (fun i => OriginalAffineLinePathSections318.restriction f L N e (g i)))
  have hr (x : OriginalLineAffineModel318.sections A L) :
      OriginalAffineLinePathSections318.restriction f L N e x ∈ Q := by
    have hx : x ∈ Submodule.span A (Set.range g) := by rw [hg]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i,rfl⟩; exact Submodule.subset_span ⟨i,rfl⟩
    · rw [← OriginalAffineLinePathSections318.unit_apply]
      simp only [map_zero]
      exact Q.zero_mem
    · intro a b _ _ ha hb
      rw [OriginalAffineLinePathSections318.restriction_add]
      exact Q.add_mem ha hb
    · intro a x _ hx
      rw [OriginalAffineLinePathSections318.restriction_smul]
      exact Q.smul_mem _ hx
  have he (z : (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections A L)) :
      (OriginalAffineLinePathSections318.comparison f L N e).hom z ∈ Q := by
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
        have ht : (b ⊗ₜ[A,f.hom] x : (ModuleCat.extendScalars f.hom).obj
            (OriginalLineAffineModel318.sections A L)) = b • ((1:B) ⊗ₜ[A,f.hom] x) := by
          rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
        rw [ht,map_smul]
        change b • (OriginalAffineLinePathSections318.comparison f L N e).hom
          ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ x) ∈ Q
        rw [OriginalAffineLinePathSections318.unit_apply]
        exact Q.smul_mem b (hr x)
    | add x y hx hy => simpa only [map_add] using Q.add_mem hx hy
  apply top_unique
  intro x hx
  obtain ⟨z,rfl⟩ := (OriginalAffineLinePathSections318.comparison f L N e).toLinearEquiv.surjective x
  exact he z

/-- A genuine rank-one frame sends that full original generator span
onto the unit ideal of the SAME target coefficient ring. -/
lemma frame_span (hg : Submodule.span A (Set.range g)=⊤)
    (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B) :
    Submodule.span B (Set.range (fun i => v (OriginalAffineLinePathSections318.restriction f L N e (g i))))=⊤ := by
  have hs := span f L N e g hg
  apply top_unique
  intro b hb
  have hv : v.symm b ∈ Submodule.span B
      (Set.range (fun i => OriginalAffineLinePathSections318.restriction f L N e (g i))) := by
    rw [hs]; trivial
  have him (x) (hx : x ∈ Submodule.span B
      (Set.range (fun i => OriginalAffineLinePathSections318.restriction f L N e (g i)))) :
      v x ∈ Submodule.span B (Set.range (fun i => v
        (OriginalAffineLinePathSections318.restriction f L N e (g i)))) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i,rfl⟩; exact Submodule.subset_span ⟨i,rfl⟩
    · simpa only [map_zero] using (Submodule.span B (Set.range (fun i => v
        (OriginalAffineLinePathSections318.restriction f L N e (g i))))).zero_mem
    · intro a b _ _ ha hb; simpa only [map_add] using Submodule.add_mem _ ha hb
    · intro a b _ hb; simpa only [map_smul] using Submodule.smul_mem _ a hb
  simpa only [LinearEquiv.apply_symm_apply] using him (v.symm b) hv
end OriginalAffineGeneratorPullback318
