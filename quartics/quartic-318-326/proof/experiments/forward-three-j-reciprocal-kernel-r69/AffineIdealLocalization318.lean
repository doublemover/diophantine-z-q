module
public import ThreeJReciprocalKernelSupport318
public section
noncomputable section
namespace AffineIdealLocalization318
open AlgebraicGeometry CategoryTheory Opposite
open AffineIdealCoordinates318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Pullback by the inverse of an actual ring isomorphism is extension by
that same isomorphism; this identity retains the whole ideal. -/
theorem comap_inverse {A B : CommRingCat.{u}} (e : A ≅ B) (I : Ideal A) :
    I.comap e.inv.hom=I.map e.hom.hom := by
  ext b
  rw [Ideal.mem_comap,Ideal.mem_map_iff_of_surjective e.hom.hom
    (ConcreteCategory.bijective_of_isIso e.hom).2]
  constructor
  · intro hb
    exact ⟨e.inv b,hb,Iso.inv_hom_id_apply e b⟩
  · rintro ⟨a,ha,rfl⟩
    simpa only [Iso.hom_inv_id_apply] using ha

/-- Ideal restriction along an affine open immersion is extension by its
actual global-section map, with the open-image isomorphism made explicit. -/
theorem top_comap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (I.comap f).ideal ⟨⊤,isAffineOpen_top X⟩=
      (I.ideal ⟨⊤,isAffineOpen_top Y⟩).map f.appTop.hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,comap_inverse]
  have hm := I.map_ideal (U:=⟨f ''ᵁ ⊤,(isAffineOpen_top X).image_of_isOpenImmersion f⟩)
    (V:=⟨⊤,isAffineOpen_top Y⟩) (by
      change f ''ᵁ ⊤ ≤ ⊤
      exact le_top)
  rw [←hm,Ideal.map_map]
  have he : Y.presheaf.map (homOfLE (show f ''ᵁ ⊤≤⊤ from le_top)).op ≫
      (f.appIso ⊤).hom=f.appTop := by
    rw [←f.app_appIso_inv ⊤,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [←CommRingCat.hom_comp,he]

/-- Canonical affine coordinates commute with restriction along the actual
Spec map. This is the needed ring/scheme bridge, not an assumed equality of
polynomial ideals after choosing unrelated chart identifications. -/
theorem coordinates_comap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]
    (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    coordinates (I.comap (Spec.map (CommRingCat.ofHom φ)))=(coordinates I).map φ := by
  unfold coordinates
  rw [top_comap,comap_inverse,comap_inverse,Ideal.map_map,Ideal.map_map]
  have he : (Spec.map (CommRingCat.ofHom φ)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv).mp
    rw [←Category.assoc,←Scheme.ΓSpecIso_inv_naturality,Category.assoc,
      Iso.inv_hom_id,Category.comp_id,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact congrArg (fun ψ => Ideal.map ψ (I.ideal ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A))⟩))
    (congrArg CommRingCat.Hom.hom he)
end AffineIdealLocalization318
