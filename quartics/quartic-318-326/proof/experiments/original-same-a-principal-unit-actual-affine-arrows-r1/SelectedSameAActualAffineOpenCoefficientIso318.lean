module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
A literal affine open immersion with known entire image detects
actual ambient sections in its genuine coefficient ring. The same
map is proved to be the expected restriction component, not an
arbitrary ring equivalence after assigning values on points.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SelectedSameAActualAffineOpenCoefficientIso318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : Scheme.{u}} {B : Type u} [CommRing B]

abbrev S (B : Type u) [CommRing B] := Spec (CommRingCat.of B)

variable (j : S B ⟶ Y) [IsOpenImmersion j] (V : Y.Opens)
variable (h : j.opensRange = V)

theorem preimage_top_of_range : j ⁻¹ᵁ V = ⊤ := by
  rw [← h, j.preimage_opensRange]

/-- The only Γ comparison is the actual map on the whole affine open
and the canonical Γ of its actual Spec coefficient ring. -/
@[expose] def coordinate : Γ(Y,V) ⟶ CommRingCat.of B :=
  j.appLE V ⊤ (preimage_top_of_range j V h).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom

include h in
theorem coordinate_isIso : IsIso (coordinate j V h) := by
  let e : (⊤ : (S B).Opens) ≤ j ⁻¹ᵁ (j ''ᵁ (⊤ : (S B).Opens)) :=
    (j.preimage_image_eq (⊤ : (S B).Opens)).ge
  have h₀ : IsIso (j.appLE (j ''ᵁ (⊤ : (S B).Opens)) ⊤ e) := by
    rw [← j.appIso_hom']
    infer_instance
  have hR : j ''ᵁ (⊤ : (S B).Opens) = V :=
    j.image_top_eq_opensRange.trans h
  have h₁ : IsIso (j.appLE V ⊤ (preimage_top_of_range j V h).ge) :=
    (j.appLE_congr e hR rfl (fun {_ _} f => IsIso f)).mp h₀
  letI := h₁
  unfold coordinate
  infer_instance

@[expose] def coordinateIso : Γ(Y,V) ≅ CommRingCat.of B := by
  letI := coordinate_isIso j V h
  exact asIso (coordinate j V h)

theorem coordinateIso_hom : (coordinateIso j V h).hom = coordinate j V h := by
  unfold coordinateIso
  rfl

variable {C : Type u} [CommRing C] (i : S C ⟶ Y) [IsOpenImmersion i]
variable (W : Y.Opens) (hW : i.opensRange = W) (hWV : W ≤ V)
variable (g : B →+* C)
variable (square : Spec.map (CommRingCat.ofHom g) ≫ j = i)

include square in
/-- The coordinate restriction is the specified actual affine map.
The proof passes through both appLE naturality equations and the same
ΓSpec square, so it retains the map on the entire section ring. -/
theorem coordinate_natural :
    Y.presheaf.map (homOfLE hWV).op ≫ coordinate i W hW =
      coordinate j V h ≫ CommRingCat.ofHom g := by
  let m := Spec.map (CommRingCat.ofHom g)
  let u : (⊤ : (S B).Opens) ≤ j ⁻¹ᵁ V := (preimage_top_of_range j V h).ge
  let v : (⊤ : (S C).Opens) ≤ i ⁻¹ᵁ W := (preimage_top_of_range i W hW).ge
  let q : (⊤ : (S C).Opens) ≤ i ⁻¹ᵁ V := v.trans (i.preimage_mono hWV)
  have hl := i.map_appLE v (homOfLE hWV).op
  have hr := Scheme.Hom.appLE_comp_appLE m j V ⊤ ⊤ u (show
    (⊤ : (S C).Opens) ≤ m ⁻¹ᵁ (⊤ : (S B).Opens) from le_rfl)
  have mt : m.appLE ⊤ ⊤ (show (⊤ : (S C).Opens) ≤
      m ⁻¹ᵁ (⊤ : (S B).Opens) from le_rfl) = m.appTop :=
    Scheme.Hom.appLE_eq_app m
  have s : m ≫ j = i := square
  have hm : j.appLE V ⊤ u ≫ m.appTop = i.appLE V ⊤ q := by
    rw [mt, s] at hr
    exact hr
  have hΓ : m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom g :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  unfold coordinate
  calc
    _ = (Y.presheaf.map (homOfLE hWV).op ≫ i.appLE W ⊤ v) ≫
        (Scheme.ΓSpecIso (CommRingCat.of C)).hom := (Category.assoc _ _ _).symm
    _ = i.appLE V ⊤ q ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom :=
      congrArg (fun c => c ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) hl
    _ = (j.appLE V ⊤ u ≫ m.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom :=
      congrArg (fun c => c ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) hm.symm
    _ = j.appLE V ⊤ u ≫ (m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) :=
      Category.assoc _ _ _
    _ = _ := by rw [hΓ, Category.assoc]

end SelectedSameAActualAffineOpenCoefficientIso318
