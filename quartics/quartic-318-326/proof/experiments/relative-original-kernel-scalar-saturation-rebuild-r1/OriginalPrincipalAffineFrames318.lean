module
public import OriginalAffineOpenFrame318
public import AffineLineFrameCover318
public section
noncomputable section
namespace OriginalPrincipalAffineFrames318
open AlgebraicGeometry CategoryTheory TopologicalSpace LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : CommRingCat.{u}) (L : Line (Spec A))
abbrev Index := AffineLineModule318.frameSet A L.object
abbrev U (r : Index A L) := AffineLineModule318.basic A r.val

lemma affine (r : Index A L) : IsAffineOpen (U A L r) :=
  IsAffineOpen.Spec_basicOpen r.val

abbrev ring (r : Index A L) := Γ(Spec A,U A L r)

/-- The ring arrow is the actual Spec preimage of the original affine-open
embedding. This avoids introducing an unrelated localization coordinate. -/
@[expose] def arrow (r : Index A L) : A ⟶ ring A L r :=
  (Scheme.Spec.preimage (affine A L r).fromSpec).unop

lemma spec_arrow (r : Index A L) : Spec.map (arrow A L r)=(affine A L r).fromSpec :=
  Scheme.Spec.image_preimage _

instance arrow_open (r : Index A L) : IsOpenImmersion (Spec.map (arrow A L r)) := by
  rw [spec_arrow]
  infer_instance

lemma arrow_range (r : Index A L) : (Spec.map (arrow A L r)).opensRange=U A L r := by
  apply TopologicalSpace.Opens.ext
  change Set.range (Spec.map (arrow A L r)) = _
  rw [spec_arrow]
  exact (affine A L r).range_fromSpec

lemma arrow_image (r : Index A L) : Spec.map (arrow A L r) ''ᵁ ⊤=U A L r :=
  (Scheme.Hom.image_top_eq_opensRange _).trans (arrow_range A L r)

@[expose] def ambientFrame (r : Index A L) :
    Γ(L.object,Spec.map (arrow A L r) ''ᵁ ⊤) ≃ₗ[Γ(Spec A,Spec.map (arrow A L r) ''ᵁ ⊤)]
      Γ(Spec A,Spec.map (arrow A L r) ''ᵁ ⊤) := by
  have e := (OpenLineSectionBasis318.sections L.object (U A L r) r.property.some).symm
  exact (arrow_image A L r).symm ▸ e

/-- Genuine frame on the literal original affine line pullback. No free
chart module is assumed, even over a nonreduced coefficient ring. -/
@[expose] def frame (r : Index A L) : OriginalLineAffineModel318.sections (ring A L r)
    (LineSheafPullback318.line (Spec.map (arrow A L r)) L) ≃ₗ[ring A L r] ring A L r :=
  OriginalAffineOpenFrame318.frame (ring A L r) (Spec.map (arrow A L r)) L (ambientFrame A L r)

/-- Every point of the original whole affine chart is covered by an
ACTUAL Spec frame map with its produced B-linear section frame. -/
theorem covers (x : Spec A) : ∃ r : Index A L, ∃ y : Spec (ring A L r),
    Spec.map (arrow A L r) y=x := by
  obtain ⟨r,hr,hf⟩ := AffineLineFrameCover318.principalCover A L.object L.opens L.cover L.frame x
  let t : Index A L := ⟨r,hf⟩
  have hx : x ∈ Set.range (affine A L t).fromSpec := by
    rw [(affine A L t).range_fromSpec]
    exact hr
  obtain ⟨y,hy⟩ := hx
  exact ⟨t,y,(congrArg (fun z : Spec (ring A L t) ⟶ Spec A => z y) (spec_arrow A L t)).trans hy⟩
end OriginalPrincipalAffineFrames318
