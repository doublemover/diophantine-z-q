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

private theorem appLE_same_hom {P Q : Scheme.{u}} {d d' : P ⟶ Q} (h : d = d')
    (V : Q.Opens) (h₁ : (⊤ : P.Opens) ≤ d ⁻¹ᵁ V) (h₂ : (⊤ : P.Opens) ≤ d' ⁻¹ᵁ V) :
    d.appLE V ⊤ h₁ = d'.appLE V ⊤ h₂ := by
  cases h
  rfl

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
  let htop : (⊤ : (S C).Opens) ≤ m ⁻¹ᵁ (⊤ : (S B).Opens) := m.preimage_top.ge
  let l : (⊤ : (S C).Opens) ≤ (i ≫ f) ⁻¹ᵁ V := h.trans (i.preimage_mono hUV)
  let r : (⊤ : (S C).Opens) ≤ (m ≫ j) ⁻¹ᵁ V := htop.trans (m.preimage_mono v)
  have left : f.appLE V U hUV ≫ i.appLE U ⊤ h = (i ≫ f).appLE V ⊤ l :=
    Scheme.Hom.appLE_comp_appLE i f V U ⊤ hUV h
  have right₀ : j.appLE V ⊤ v ≫ m.appLE ⊤ ⊤ htop = (m ≫ j).appLE V ⊤ r :=
    Scheme.Hom.appLE_comp_appLE m j V ⊤ ⊤ v htop
  have hmap : m.appLE ⊤ ⊤ htop = m.appTop := Scheme.Hom.appLE_eq_app m
  have hm : m ≫ j = i ≫ f := square
  have right : j.appLE V ⊤ v ≫ m.appTop = (i ≫ f).appLE V ⊤ l :=
    (congrArg (fun g' : Γ(S B,⊤) ⟶ Γ(S C,⊤) => j.appLE V ⊤ v ≫ g') hmap.symm).trans
      (right₀.trans (appLE_same_hom hm V r l))
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
  let hU : U ≤ f ⁻¹ᵁ (⊤ : (S B).Opens) := le_top.trans f.preimage_top.ge
  let hL : (⊤ : (S C).Opens) ≤ (i ≫ f) ⁻¹ᵁ (⊤ : (S B).Opens) :=
    h.trans (i.preimage_mono hU)
  let hR : (⊤ : (S C).Opens) ≤ m ⁻¹ᵁ (⊤ : (S B).Opens) := m.preimage_top.ge
  have he₀ : f.appLE ⊤ U hU ≫ i.appLE U ⊤ h = (i ≫ f).appLE ⊤ ⊤ hL :=
    Scheme.Hom.appLE_comp_appLE i f ⊤ U ⊤ hU h
  have mtop : m.appLE ⊤ ⊤ hR = m.appTop := Scheme.Hom.appLE_eq_app m
  have he : f.appLE ⊤ U hU ≫ i.appLE U ⊤ h = m.appTop :=
    he₀.trans ((appLE_same_hom hm ⊤ hL hR).trans mtop)
  change f.appLE ⊤ U hU ≫ (i.appLE U ⊤ h ≫ _) = _
  rw [← Category.assoc, he]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

end SelectedSameAAffineCoordinatePullback318
