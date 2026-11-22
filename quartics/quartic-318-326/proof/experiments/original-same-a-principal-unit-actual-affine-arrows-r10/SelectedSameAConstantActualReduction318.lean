module

public import SelectedSameAConstantAffineCoverProduced318
public import SelectedSameADualNumberPointSurjectivity318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The entire constant fibre is the same marked A, not an independently supplied reduction
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace SelectedSameAConstantActualReduction318

open SelectedSameADualNumberPointSurjectivity318
open SelectedSameAConstantAffineCoverProduced318
open SelectedSameAConstantTargetTriangle318
open SelectedSameAConstantDualNumberBaseChange318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
variable {A : Scheme.{u}} (a : A ⟶ S k)

theorem reduction_base :
    reductionMap k ≫ base k = 𝟙 (S k) := by
  change sp (TrivSqZeroExt.fstHom k k k).toRingHom ≫ sp (algebraMap k (D k)) = _
  let K := CommRingCat.of k
  let C := CommRingCat.of (D k)
  let d : K ⟶ C := CommRingCat.ofHom (algebraMap k (D k))
  let r : C ⟶ K := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : d ≫ r = 𝟙 K := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact TrivSqZeroExt.fst_inl k b
  exact (Spec.map_comp d r).symm.trans
    ((congrArg (fun f : K ⟶ K => Spec.map f) hr).trans (Spec.map_id K))

/-- The actual original surface, with its fixed marking, sits in the
chosen constant family by its literal closed reduction. -/
@[expose] def constantReduction : A ⟶ pullback a (base k) :=
  pullback.lift (𝟙 A) (a ≫ reductionMap k)
    (by rw [Category.id_comp, Category.assoc, reduction_base, Category.comp_id])

@[reassoc]
theorem constantReduction_fst :
    constantReduction a ≫ pullback.fst a (base k) = 𝟙 A :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem constantReduction_snd :
    constantReduction a ≫ pullback.snd a (base k) = a ≫ reductionMap k :=
  pullback.lift_snd _ _ _

theorem constantReduction_pullback :
    IsPullback (constantReduction a) a (pullback.snd a (base k)) (reductionMap k) := by
  have hOuter : IsPullback (constantReduction a ≫ pullback.fst a (base k)) a a
      (reductionMap k ≫ base k) := by
    rw [constantReduction_fst, reduction_base]
    apply IsPullback.of_horiz_isIso
    constructor
    simp only [Category.id_comp, Category.comp_id]
  exact hOuter.of_right (constantReduction_snd a) (IsPullback.of_hasPullback a (base k))

theorem constantReduction_closed : IsClosedImmersion (constantReduction a) := by
  have hp : Function.Surjective ((TrivSqZeroExt.fstHom k k k).toRingHom) := by
    intro b
    exact ⟨TrivSqZeroExt.inl b, TrivSqZeroExt.fst_inl k b⟩
  have hh : IsClosedImmersion (reductionMap k) := IsClosedImmersion.spec_of_surjective _ hp
  exact MorphismProperty.of_isPullback (constantReduction_pullback a).flip hh

theorem constantReduction_onto : Function.Surjective (constantReduction a) :=
  closed_points_onto k (pullback.snd a (base k)) (constantReduction a) a (constantReduction_pullback a)

variable {B : Type u} [CommRing B] [Algebra k B]

/-- The full affine closed-fibre marking actually commutes with the
original affine's map into the same global constant family. -/
theorem constant_chart_on_closed_fibre (j : S B ⟶ A) (hj : j ≫ a = sp (algebraMap k B)) :
    sp (TrivSqZeroExt.fstHom B B B).toRingHom ≫ constantAffineMap a j hj =
      j ≫ constantReduction a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, constantAffineMap_fst, constantReduction_fst, Category.comp_id]
    have h : sp (TrivSqZeroExt.fstHom B B B).toRingHom ≫ sp (TrivSqZeroExt.inlHom B B) = 𝟙 (S B) := by
      let C := CommRingCat.of B
      let E := CommRingCat.of (TrivSqZeroExt B B)
      let d : C ⟶ E := CommRingCat.ofHom (TrivSqZeroExt.inlHom B B)
      let r : E ⟶ C := CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom
      have hr : d ≫ r = 𝟙 C := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro b
        exact TrivSqZeroExt.fst_inl B b
      exact (Spec.map_comp d r).symm.trans
        ((congrArg (fun f : C ⟶ C => Spec.map f) hr).trans (Spec.map_id C))
    rw [← Category.assoc, h, Category.id_comp]
  · simp only [Category.assoc, constantAffineMap_snd, constantReduction_snd]
    rw [← Category.assoc j a, hj, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact coeffMap_fst (algebraMap k B) z

end SelectedSameAConstantActualReduction318
