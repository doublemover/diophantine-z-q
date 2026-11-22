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

private theorem affine_base_commutes :
    CommSq (sp (TrivSqZeroExt.inlHom B B)) (sp (coeffMap (algebraMap k B)))
      (sp (algebraMap k B)) (base k) := by
  constructor
  change sp (TrivSqZeroExt.inlHom B B) ≫ sp (algebraMap k B) =
    sp (coeffMap (algebraMap k B)) ≫ sp (algebraMap k (D k))
  calc
    _ = sp ((TrivSqZeroExt.inlHom B B).comp (algebraMap k B)) :=
      (Spec.map_comp (CommRingCat.ofHom (algebraMap k B))
        (CommRingCat.ofHom (TrivSqZeroExt.inlHom B B))).symm
    _ = sp ((coeffMap (algebraMap k B)).comp (algebraMap k (D k))) :=
      congrArg (fun m : k →+* TrivSqZeroExt B B => sp m)
        (coeffMap_constants_comp (k := k) (B := B))
    _ = sp (coeffMap (algebraMap k B)) ≫ sp (algebraMap k (D k)) :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap k (D k)))
        (CommRingCat.ofHom (coeffMap (algebraMap k B)))

set_option maxHeartbeats 1000000 in
/-- The genuine constant affine ring chart has exactly the two stated
projections, by the literal tensor ring and no chosen section. -/
theorem affine_base_pullback :
    IsPullback (sp (TrivSqZeroExt.inlHom B B)) (sp (coeffMap (algebraMap k B)))
      (sp (algebraMap k B)) (base k) := by
  let T := B ⊗[k] D k
  let E : T ≃+* TrivSqZeroExt B B := tensorIso (k := k) (B := B)
  let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : D k →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let e : S (TrivSqZeroExt B B) ≅ S T := Scheme.Spec.mapIso E.toCommRingCatIso.op
  let p : pullback (sp (algebraMap k B)) (base k) ≅ S T := pullbackSpecIso k B (D k)
  let j : S (TrivSqZeroExt B B) ≅ pullback (sp (algebraMap k B)) (base k) := e ≪≫ p.symm
  have he : e.hom = sp E.toRingHom := by
    rfl
  have hl : E.toRingHom.comp l = TrivSqZeroExt.inlHom B B := by
    apply RingHom.ext
    intro b
    exact tensorIso_from_chart (k := k) (B := B) b
  have hr : E.toRingHom.comp r = coeffMap (algebraMap k B) := by
    apply RingHom.ext
    intro z
    exact tensorIso_from_base (k := k) (B := B) z
  have hpl : p.inv ≫ pullback.fst (sp (algebraMap k B)) (base k) = sp l :=
    pullbackSpecIso_inv_fst k B (D k)
  have hpr : p.inv ≫ pullback.snd (sp (algebraMap k B)) (base k) = sp r :=
    pullbackSpecIso_inv_snd k B (D k)
  have h1 : j.hom ≫ pullback.fst (sp (algebraMap k B)) (base k) =
      sp (TrivSqZeroExt.inlHom B B) := by
    change (e.hom ≫ p.inv) ≫ pullback.fst (sp (algebraMap k B)) (base k) = _
    calc
      _ = e.hom ≫ sp l := (Category.assoc _ _ _).trans
        (congrArg (fun m : S T ⟶ S B => e.hom ≫ m) hpl)
      _ = sp E.toRingHom ≫ sp l := congrArg (fun m : S (TrivSqZeroExt B B) ⟶ S T => m ≫ sp l) he
      _ = sp (E.toRingHom.comp l) :=
        (Spec.map_comp (CommRingCat.ofHom l) (CommRingCat.ofHom E.toRingHom)).symm
      _ = sp (TrivSqZeroExt.inlHom B B) := congrArg (fun m => sp m) hl
  have h2 : j.hom ≫ pullback.snd (sp (algebraMap k B)) (base k) =
      sp (coeffMap (algebraMap k B)) := by
    change (e.hom ≫ p.inv) ≫ pullback.snd (sp (algebraMap k B)) (base k) = _
    calc
      _ = e.hom ≫ sp r := (Category.assoc _ _ _).trans
        (congrArg (fun m : S T ⟶ S (D k) => e.hom ≫ m) hpr)
      _ = sp E.toRingHom ≫ sp r := congrArg (fun m : S (TrivSqZeroExt B B) ⟶ S T => m ≫ sp r) he
      _ = sp (E.toRingHom.comp r) :=
        (Spec.map_comp (CommRingCat.ofHom r) (CommRingCat.ofHom E.toRingHom)).symm
      _ = sp (coeffMap (algebraMap k B)) := congrArg (fun m => sp m) hr
  exact IsPullback.of_iso_pullback (affine_base_commutes (k := k) (B := B)) j h1 h2

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
