module

public import SelectedSameAActualAffineOpenCoefficientIso318
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
The literal top sections of restriction to an actual affine chart
and the genuine ambient section ring of that chart. The scalar
comparison uses its canonical Gamma comparison, not a numerical
or abstract affine-basis identification.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAActualAffineAmbientTop318

open SelectedSameAActualAffineOpenCoefficientIso318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Scheme.{u}} {B : Type u} [CommRing B]
variable (j : S B ⟶ A) [IsOpenImmersion j]

abbrev W := j.opensRange
abbrev Q := CommRingCat.of B
abbrev R := Γ(A,W j)
abbrev Γj := moduleSpecΓFunctor (R := Q (B := B))

/-- Opposite-direction actual restriction from the full image of the
affine chart's top open to its equal declared range. -/
abbrev topTransition : op (j ''ᵁ (⊤ : (S B).Opens)) ⟶ op (W j) :=
  (eqToHom j.image_top_eq_opensRange.symm).op

@[expose] def topAdd (M : A.Modules) : Γ(M.restrict j,⊤) ≅ Γ(M,W j) :=
  M.restrictAppIso j ⊤ ≪≫
    M.presheaf.mapIso (eqToIso j.image_top_eq_opensRange.symm).op

/-- The actual global comparison sends the original ring map back
to its canonical coordinate. -/
theorem ring_comparison :
    A.presheaf.map (topTransition j) ≫ coordinate j (W j) rfl =
      (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (Q (B := B))).hom := by
  unfold coordinate
  rw [← Category.assoc, j.appIso_hom']
  let T := (j ''ᵁ (⊤ : (S B).Opens))
  let h := (preimage_top_of_range j (W j) rfl).ge
  have e : topTransition j = (homOfLE (show T ≤ W j from j.image_top_eq_opensRange.le)).op :=
    Subsingleton.elim _ _
  rw [e, j.map_appLE]

theorem ring_inverse (b : B) :
    A.presheaf.map (topTransition j)
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (Q (B := B))).inv b)) =
        (coordinateIso j (W j) rfl).inv b := by
  apply (ConcreteCategory.bijective_of_isIso (coordinateIso j (W j) rfl).hom).1
  let c := (Scheme.ΓSpecIso (Q (B := B))).inv b
  have h := congrArg (fun g => g ((j.appIso ⊤).inv c)) (ring_comparison j)
  rw [coordinateIso_hom]
  change coordinate j (W j) rfl (A.presheaf.map (topTransition j) ((j.appIso ⊤).inv c)) =
    coordinate j (W j) rfl ((coordinateIso j (W j) rfl).inv b)
  have hL : coordinate j (W j) rfl ((coordinateIso j (W j) rfl).inv b) = b := by
    rw [← coordinateIso_hom]
    exact Iso.inv_hom_id_apply _ b
  rw [hL]
  change coordinate j (W j) rfl (A.presheaf.map (topTransition j) ((j.appIso ⊤).inv c)) =
    (Scheme.ΓSpecIso (Q (B := B))).hom ((j.appIso ⊤).hom ((j.appIso ⊤).inv c)) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.trans (Iso.inv_hom_id_apply _ b)

/-- Exact chart scalar compatibility for that same top-additive map. -/
theorem topAdd_smul (M : A.Modules) (b : B)
    (z : (Γj (B := B)).obj (M.restrict j)) :
    (topAdd j M).hom (b • z) = (coordinateIso j (W j) rfl).inv b • (topAdd j M).hom z := by
  let z' : Γ(M.restrict j,⊤) := z
  let b' : Γ(S B,⊤) := (Scheme.ΓSpecIso (Q (B := B))).inv b
  let t := (M.restrictAppIso j ⊤).hom z'
  let r := topTransition j
  have hfirst : (show Γ(M.restrict j,⊤) from b • z) = b' • z' := by
    change ((S B).presheaf.map (𝟙 (op ⊤))) b' • z' = b' • z'
    have hi := congrArg (fun f : Γ(S B,⊤) ⟶ Γ(S B,⊤) => f b')
      ((S B).presheaf.map_id (op ⊤))
    exact congrArg (fun y : Γ(S B,⊤) => y • z') hi
  have h1 : (M.restrictAppIso j ⊤).hom (b' • z') =
      (j.appIso ⊤).inv b' • t :=
    Scheme.Modules.smul_restrictAppIso_hom_apply j M ⊤ b' z'
  have h2 : M.presheaf.map r ((j.appIso ⊤).inv b' • t) =
      A.presheaf.map r ((j.appIso ⊤).inv b') • M.presheaf.map r t :=
    M.val.map_smul r _ t
  change M.presheaf.map r ((M.restrictAppIso j ⊤).hom
    (show Γ(M.restrict j,⊤) from b • z)) =
      (coordinateIso j (W j) rfl).inv b • M.presheaf.map r t
  rw [hfirst, h1, h2, ring_inverse j b]

/-- Transporting the restricted morphism to the actual ambient sections
is just its own evaluation on that actual open. -/
theorem topAdd_map {M N : A.Modules} (φ : M ⟶ N)
    (z : (Γj (B := B)).obj (M.restrict j)) :
    (topAdd j N).hom ((Γj (B := B)).map ((Scheme.Modules.restrictFunctor j).map φ) z) =
      φ.app (W j) ((topAdd j M).hom z) := by
  let T := j ''ᵁ (⊤ : (S B).Opens)
  let g := topTransition j
  change N.presheaf.map g (φ.app T (show Γ(M,T) from z)) =
    φ.app (W j) (M.presheaf.map g (show Γ(M,T) from z))
  exact (congrArg (fun m => m (show Γ(M,T) from z)) (φ.mapPresheaf.naturality g)).symm

end SelectedSameAActualAffineAmbientTop318
