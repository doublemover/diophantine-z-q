module

public import SelectedSameAConstantTargetTriangle318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Produce the actual constant-family affine open cover

Every constant chart is the pullback of the literal old affine open.
This proves, rather than assumes, its open-immersion and cover.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

namespace SelectedSameAConstantAffineCoverProduced318

open SelectedSameAConstantDualNumberBaseChange318
open SelectedSameAConstantTargetTriangle318

universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev D (k : Type u) [CommRing k] := TrivSqZeroExt k k
abbrev base (k : Type u) [CommRing k] := sp (algebraMap k (D k))

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]

/-- The genuine constant affine ring chart has exactly the two stated
projections, by the literal tensor ring and no chosen section. -/
theorem affine_base_pullback :
    IsPullback (sp (TrivSqZeroExt.inlHom B B)) (sp (coeffMap (algebraMap k B)))
      (sp (algebraMap k B)) (base k) := by
  let T := B ⊗[k] D k
  let e : S (TrivSqZeroExt B B) ≅ S T :=
    Scheme.Spec.mapIso (tensorIso (k := k) (B := B)).toCommRingCatIso.op
  let p := pullbackSpecIso k B (D k)
  let j : S (TrivSqZeroExt B B) ≅ pullback (sp (algebraMap k B)) (base k) := e ≪≫ p.symm
  have h1 : j.hom ≫ pullback.fst (sp (algebraMap k B)) (base k) =
      sp (TrivSqZeroExt.inlHom B B) := by
    change (e.hom ≫ p.inv) ≫ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_fst]
    change sp (tensorIso (k := k) (B := B)).toRingHom ≫
      sp (Algebra.TensorProduct.includeLeftRingHom : B →+* T) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    intro b
    exact tensorIso_from_chart (k := k) (B := B) b
  have h2 : j.hom ≫ pullback.snd (sp (algebraMap k B)) (base k) =
      sp (coeffMap (algebraMap k B)) := by
    change (e.hom ≫ p.inv) ≫ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_snd]
    change sp (tensorIso (k := k) (B := B)).toRingHom ≫
      sp (Algebra.TensorProduct.includeRight.toRingHom : D k →+* T) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    intro z
    exact tensorIso_from_base (k := k) (B := B) z
  apply IsPullback.of_iso_pullback _ j h1 h2
  constructor
  calc
    sp (TrivSqZeroExt.inlHom B B) ≫ sp (algebraMap k B) =
      (j.hom ≫ pullback.fst (sp (algebraMap k B)) (base k)) ≫ sp (algebraMap k B) :=
      congrArg (fun f => f ≫ sp (algebraMap k B)) h1.symm
    _ = (j.hom ≫ pullback.snd (sp (algebraMap k B)) (base k)) ≫ base k := by
      simp only [Category.assoc, pullback.condition]
    _ = _ := congrArg (fun f => f ≫ base k) h2

variable {A : Scheme.{u}} (a : A ⟶ S k)
variable (j : S B ⟶ A) (hj : j ≫ a = sp (algebraMap k B))

/-- The affine piece is the genuine inverse image of j in the selected
constant family. Pasting cancellation uses the specified true leg. -/
theorem constant_chart_pullback :
    IsPullback (sp (TrivSqZeroExt.inlHom B B)) (constantAffineMap a j hj)
      j (pullback.fst a (base k)) := by
  have hout : IsPullback (sp (TrivSqZeroExt.inlHom B B))
      (constantAffineMap a j hj ≫ pullback.snd a (base k)) (j ≫ a) (base k) := by
    rw [constantAffineMap_snd, hj]
    exact affine_base_pullback
  exact hout.of_bot (constantAffineMap_fst a j hj).symm (IsPullback.of_hasPullback a (base k))

/-- This derives the open-immersion property of the real target
constant chart, rather than taking it as a gluing interface. -/
theorem constant_chart_open [IsOpenImmersion j] :
    IsOpenImmersion (constantAffineMap a j hj) :=
  MorphismProperty.of_isPullback (constant_chart_pullback a j hj) inferInstance

/-- The original genuine affine opens give a genuine covering family on
the actual constant thickening. All source chart points are produced by
the real pullback carrier theorem. -/
theorem constant_charts_cover {I : Type v}
    (Bᵢ : I → Type u) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra k (Bᵢ i)]
    (jᵢ : ∀ i, S (Bᵢ i) ⟶ A)
    (hᵢ : ∀ i, jᵢ i ≫ a = sp (algebraMap k (Bᵢ i)))
    (hCover : ∀ y : A, ∃ (i : I) (x : S (Bᵢ i)), jᵢ i x = y)
    (z : pullback a (base k)) :
    ∃ (i : I) (x : S (TrivSqZeroExt (Bᵢ i) (Bᵢ i))), constantAffineMap a (jᵢ i) (hᵢ i) x = z := by
  obtain ⟨i, x, hx⟩ := hCover (pullback.fst a (base k) z)
  obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback
    (constant_chart_pullback a (jᵢ i) (hᵢ i)) x z hx
  exact ⟨i, y, hy⟩

end SelectedSameAConstantAffineCoverProduced318
