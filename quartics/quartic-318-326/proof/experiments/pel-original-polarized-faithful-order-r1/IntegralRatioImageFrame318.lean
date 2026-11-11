module
public import OpenModuleBaseChangeGenerators318
public import RestrictedFreeScalarRow318
public import LocallyPrincipalImageFrame318
public section
noncomputable section
namespace IntegralRatioImageFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GlobalScalarSheafEndomorphism318 IntegralOpenUnitMonomorphism318
variable {X U V W : Scheme} {ι : Type*}
variable (right : W ⟶ V) (left : W ⟶ U) (k : V ⟶ X) (j : U ⟶ X)
  [IsOpenImmersion right] [IsOpenImmersion left] [IsOpenImmersion k] [IsOpenImmersion j]
  (H : IsPullback right left k j) [IsIntegral V] [Nonempty W]
variable (r : ι → Γ(U,⊤)) (c : ι → Γ(V,⊤)) (t : Γ(W,⊤)ˣ)
  (h : ∀ i, left.appTop (r i) = right.appTop (c i) * (t : Γ(W,⊤)))

/-- The actual direct-image Cartesian isomorphism, including its structure
module comparison, for an arbitrary genuine integral open chart. -/
abbrev ambientIso := OpenModuleBaseChangeUnit318.unitIso right left k j H

/-- A generator in the original rational ambient sheaf. Its multiplier
is a specified actual regular unit on the entire scheme intersection. -/
@[expose] def generator : SheafOfModules.unit V.ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor k).obj (ChartGeneratedImageSheaf318.ambient j) :=
  unitMap right ≫ (Scheme.Modules.pushforward right).map (unitIso W t).hom ≫
    (ambientIso right left k j H).inv

instance generator_mono : Mono (generator right left k j H t) := by
  dsimp [generator]
  infer_instance

include h in
/-- Exact normalized coefficient equation for every genuine global
image generator. No assertion about sectionwise images is used. -/
theorem generator_coefficient (i : ι) :
    (Scheme.Modules.restrictFunctor k).map (ChartGeneratedImageSheaf318.generator j r i) =
      (Scheme.Modules.restrictUnitIso k).hom ≫ endomorphism V (c i) ≫
        generator right left k j H t := by
  apply (cancel_epi (Scheme.Modules.restrictUnitIso k).inv).1
  apply (cancel_mono (ambientIso right left k j H).hom).1
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [generator]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [OpenModuleBaseChangeGenerators318.generator_square right left k j H r i]
  change _ = endomorphism V (c i) ≫ unitMap right ≫
    (Scheme.Modules.pushforward right).map (endomorphism W (t : Γ(W,⊤)))
  rw [OpenScalarSheafNaturality318.unit_scalar_square,Category.assoc,
    ←Functor.map_comp,endomorphism_comp,←h i]

include h in
lemma presentation_factorization :
    RestrictedFreeScalarRow318.row k c ≫ generator right left k j H t =
      (Scheme.Modules.restrictFunctor k).map (ChartGeneratedImageSheaf318.presentation j r) := by
  apply RestrictedFreeScalarRow318.factorization
  intro i
  rw [ChartGeneratedImageSheaf318.generator_presentation]
  exact generator_coefficient right left k j H r c t h i

/-- Genuine rank-one frame for the whole categorical image on the WHOLE
open V, not just on its intersection with the chosen rational anchor.
The coefficient row is split by the supplied literal coordinate ONE. -/
@[expose] def frame (i : ι) (hi : c i = 1) :
    SheafOfModules.unit V.ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor k).obj (ChartGeneratedImageSheaf318.sheaf j r) := by
  letI := RestrictedFreeScalarRow318.row_epi k c i hi
  exact LocallyPrincipalImageFrame318.frame k (ChartGeneratedImageSheaf318.presentation j r)
    (RestrictedFreeScalarRow318.row k c) (generator right left k j H t)
    (presentation_factorization right left k j H r c t h)

@[reassoc] theorem frame_inclusion (i : ι) (hi : c i = 1) :
    (frame right left k j H r c t h i hi).hom ≫
      (Scheme.Modules.restrictFunctor k).map
        (image.ι (ChartGeneratedImageSheaf318.presentation j r)) =
      generator right left k j H t :=
  LocallyPrincipalImageFrame318.frame_inclusion _ _ _ _ _

/-- The actual image-factor global section has the asserted entire
regular coefficient in the produced frame. -/
theorem section_in_frame (i : ι) (hi : c i = 1) (a : ι) :
    (Scheme.Modules.restrictUnitIso k).inv ≫ (Scheme.Modules.restrictFunctor k).map
      (SheafOfModules.ιFree a ≫ factorThruImage
        (ChartGeneratedImageSheaf318.presentation j r)) =
      endomorphism V (c a) ≫ (frame right left k j H r c t h i hi).hom := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctor k).map
    (image.ι (ChartGeneratedImageSheaf318.presentation j r)))).1
  rw [Category.assoc,frame_inclusion,←Functor.map_comp,Category.assoc,
    image.fac,ChartGeneratedImageSheaf318.generator_presentation,
    generator_coefficient right left k j H r c t h a]
  simp only [Iso.inv_hom_id_assoc,Category.assoc]
end IntegralRatioImageFrame318
