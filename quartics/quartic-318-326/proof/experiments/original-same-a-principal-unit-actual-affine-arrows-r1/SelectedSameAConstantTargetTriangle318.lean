module

public import SelectedSameAConstantDualNumberBaseChange318
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Produce the target restriction triangle in the actual constant family

The target is the literal pullback of the original closed fibre along the
fixed dual-number base. Its affine maps do not use a deformation chart.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SelectedSameAConstantTargetTriangle318

open SelectedSameAConstantDualNumberBaseChange318

universe u
variable {k B B' : Type u} [CommRing k] [CommRing B] [CommRing B']
  [Algebra k B] [Algebra k B']

abbrev S (A : Type u) [CommRing A] : Scheme.{u} := Spec (CommRingCat.of A)
abbrev sp {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C) :
    S C ⟶ S A := Spec.map (CommRingCat.ofHom f)

private theorem sp_comp {A C E : Type u} [CommRing A] [CommRing C] [CommRing E]
    (f : A →+* C) (g : C →+* E) : sp g ≫ sp f = sp (g.comp f) := by
  rw [← Spec.map_comp] <;> rfl

local notation "D" => TrivSqZeroExt k k
local notation "T" => TrivSqZeroExt B B
local notation "T'" => TrivSqZeroExt B' B'

variable {R : Scheme.{u}} (r : R ⟶ S k)

/-- The actual chart map to the constant family, by the literal pullback. -/
noncomputable def constantAffineMap (a : S B ⟶ R)
    (ha : a ≫ r = sp (algebraMap k B)) :
    S T ⟶ pullback r (sp (algebraMap k D)) :=
  pullback.lift (sp (TrivSqZeroExt.inlHom B B) ≫ a) (sp (coeffMap (algebraMap k B)))
    (by rw [Category.assoc, ha, sp_comp, sp_comp, coeffMap_constants_comp])

theorem constantAffineMap_fst (a : S B ⟶ R) (ha : a ≫ r = sp (algebraMap k B)) :
    constantAffineMap r a ha ≫ pullback.fst r (sp (algebraMap k D)) =
      sp (TrivSqZeroExt.inlHom B B) ≫ a := by
  unfold constantAffineMap
  simp only [pullback.lift_fst]

theorem constantAffineMap_snd (a : S B ⟶ R) (ha : a ≫ r = sp (algebraMap k B)) :
    constantAffineMap r a ha ≫ pullback.snd r (sp (algebraMap k D)) =
      sp (coeffMap (algebraMap k B)) := by
  unfold constantAffineMap
  simp only [pullback.lift_snd]

/-- A genuine restriction of the original reduced chart gives the equality
of the actual constant-family pieces, with the same dual-number base. -/
theorem constantAffineMap_restriction
    (a : S B ⟶ R) (a' : S B' ⟶ R)
    (ha : a ≫ r = sp (algebraMap k B)) (ha' : a' ≫ r = sp (algebraMap k B'))
    (f : B →ₐ[k] B') (hf : sp f.toRingHom ≫ a = a') :
    sp (coeffMap f.toRingHom) ≫ constantAffineMap r a ha = constantAffineMap r a' ha' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, constantAffineMap_fst]
    calc
      sp (coeffMap f.toRingHom) ≫ sp (TrivSqZeroExt.inlHom B B) ≫ a =
          (sp (coeffMap f.toRingHom) ≫ sp (TrivSqZeroExt.inlHom B B)) ≫ a :=
        (Category.assoc _ _ _).symm
      _ = (sp (TrivSqZeroExt.inlHom B' B') ≫ sp f.toRingHom) ≫ a := by
        rw [sp_comp, coeffMap_chart_comp, ← sp_comp]
      _ = sp (TrivSqZeroExt.inlHom B' B') ≫ a' := by rw [Category.assoc, hf]
  · simp only [Category.assoc, constantAffineMap_snd, sp_comp, coeffMap_base_comp]

/-- In particular both routes from a common reduced open are the same
as maps to Y, before comparing any chart of the deformed scheme. -/
theorem common_constant_triangle {C : Type u} [CommRing C] [Algebra k C]
    (a : S B ⟶ R) (a' : S B' ⟶ R) (w : S C ⟶ R)
    (ha : a ≫ r = sp (algebraMap k B)) (ha' : a' ≫ r = sp (algebraMap k B'))
    (hw : w ≫ r = sp (algebraMap k C)) (f : B →ₐ[k] C) (g : B' →ₐ[k] C)
    (hf : sp f.toRingHom ≫ a = w) (hg : sp g.toRingHom ≫ a' = w) :
    sp (coeffMap f.toRingHom) ≫ constantAffineMap r a ha =
      sp (coeffMap g.toRingHom) ≫ constantAffineMap r a' ha' :=
  (constantAffineMap_restriction r a w ha hw f hf).trans
    (constantAffineMap_restriction r a' w ha' hw g hg).symm

end SelectedSameAConstantTargetTriangle318
