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
abbrev base (k : Type u) [CommRing k] : S (D k) ⟶ S k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (D k)))

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]

/-- All nontrivial transport is in the four literal coefficient
rings, before applying the contravariant Spec functor. -/
private theorem affine_base_ring_pushout :
    IsPushout (CommRingCat.ofHom (algebraMap k B))
      (CommRingCat.ofHom (algebraMap k (D k)))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom B B))
      (CommRingCat.ofHom (coeffMap (algebraMap k B))) := by
  let T := B ⊗[k] D k
  let K := CommRingCat.of k
  let C := CommRingCat.of B
  let D₀ := CommRingCat.of (D k)
  let U := CommRingCat.of (TrivSqZeroExt B B)
  let T₀ := CommRingCat.of T
  let c : K ⟶ C := CommRingCat.ofHom (algebraMap k B)
  let d : K ⟶ D₀ := CommRingCat.ofHom (algebraMap k (D k))
  let l : C ⟶ T₀ := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let r : D₀ ⟶ T₀ := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l' : C ⟶ U := CommRingCat.ofHom (TrivSqZeroExt.inlHom B B)
  let r' : D₀ ⟶ U := CommRingCat.ofHom (coeffMap (algebraMap k B))
  let e : T₀ ≅ U := (tensorIso (k := k) (B := B)).toCommRingCatIso
  have hp : IsPushout c d l r := CommRingCat.isPushout_tensorProduct k B (D k)
  have hl : l ≫ e.hom = (Iso.refl C).hom ≫ l' := by
    rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact tensorIso_from_chart (k := k) (B := B) b
  have hr : r ≫ e.hom = (Iso.refl D₀).hom ≫ r' := by
    rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact tensorIso_from_base (k := k) (B := B) z
  have hc : c ≫ (Iso.refl C).hom = (Iso.refl K).hom ≫ c := by simp
  have hd : d ≫ (Iso.refl D₀).hom = (Iso.refl K).hom ≫ d := by simp
  exact hp.of_iso (Iso.refl K) (Iso.refl C) (Iso.refl D₀) e hc hd hl hr

/-- The genuine constant affine ring chart has exactly the two stated
projections, by the literal tensor ring and no chosen section. -/
theorem affine_base_pullback :
    IsPullback (sp (TrivSqZeroExt.inlHom B B)) (sp (coeffMap (algebraMap k B)))
      (sp (algebraMap k B)) (base k) :=
  isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap k B)) (CommRingCat.ofHom (algebraMap k (D k)))
    (CommRingCat.ofHom (TrivSqZeroExt.inlHom B B))
    (CommRingCat.ofHom (coeffMap (algebraMap k B)))
    (affine_base_ring_pushout (k := k) (B := B))

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
    (z : ↥(pullback a (base k) : Scheme.{u})) :
    ∃ (i : I) (x : S (TrivSqZeroExt (Bᵢ i) (Bᵢ i))), constantAffineMap a (jᵢ i) (hᵢ i) x = z := by
  obtain ⟨i, x, hx⟩ := hCover (pullback.fst a (base k) z)
  obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback
    (constant_chart_pullback a (jᵢ i) (hᵢ i)) x z hx
  exact ⟨i, y, hy⟩

end SelectedSameAConstantAffineCoverProduced318
