module

public import SelectedSameAActualAffineOpenCoefficientIso318

/-! Pullback of genuine scheme sections, resolved through both literal
affine coordinates, is precisely the specified whole-Spec ring map. -/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedSameAAffineCoordinatePullback318

open SelectedSameAActualAffineOpenCoefficientIso318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {B C : Type u} [CommRing B] [CommRing C]

theorem coordinate_pullback (f : X ⟶ Y)
    (j : S B ⟶ Y) (i : S C ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i]
    (V : Y.Opens) (U : X.Opens)
    (hj : j.opensRange = V) (hi : i.opensRange = U)
    (hUV : U ≤ f ⁻¹ᵁ V) (g : B →+* C)
    (square : Spec.map (CommRingCat.ofHom g) ≫ j = i ≫ f) :
    f.appLE V U hUV ≫ coordinate i U hi = coordinate j V hj ≫ CommRingCat.ofHom g := by
  let m := Spec.map (CommRingCat.ofHom g)
  let v := (preimage_top_of_range j V hj).ge
  let h := (preimage_top_of_range i U hi).ge
  have htop : (⊤ : (S C).Opens) ≤ m ⁻¹ᵁ (⊤ : (S B).Opens) := le_rfl
  have left := Scheme.Hom.appLE_comp_appLE i f V U ⊤ hUV h
  have right := Scheme.Hom.appLE_comp_appLE m j V ⊤ ⊤ v htop
  have hmap : m.appLE ⊤ ⊤ htop = m.appTop := Scheme.Hom.appLE_eq_app m
  have hm : m ≫ j = i ≫ f := square
  rw [hmap, hm] at right
  have hΓ : m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom g :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  unfold coordinate
  rw [← Category.assoc, left, ← right, Category.assoc, hΓ, Category.assoc]

/-- Pullback of one global coefficient through the original affine map,
without replacing it by evaluation at a point. -/
theorem coordinate_pullback_global (f : Y ⟶ S B)
    (i : S C ⟶ Y) [IsOpenImmersion i]
    (U : Y.Opens) (hi : i.opensRange = U) (g : B →+* C)
    (square : i ≫ f = Spec.map (CommRingCat.ofHom g)) :
    f.appLE ⊤ U le_top ≫ coordinate i U hi =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom g := by
  let m := Spec.map (CommRingCat.ofHom g)
  have hm : i ≫ f = m := square
  let h := (preimage_top_of_range i U hi).ge
  have he := Scheme.Hom.appLE_comp_appLE i f ⊤ U ⊤ le_top h
  rw [hm, Scheme.Hom.appLE_eq_app] at he
  unfold coordinate
  rw [← Category.assoc, he]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

end SelectedSameAAffineCoordinatePullback318
