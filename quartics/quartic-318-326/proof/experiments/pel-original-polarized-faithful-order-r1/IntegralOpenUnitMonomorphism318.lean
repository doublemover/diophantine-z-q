module
public import OpenRestrictionImages318
public import Mathlib.AlgebraicGeometry.FunctionField
public section
noncomputable section
namespace IntegralOpenUnitMonomorphism318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {U X : Scheme} (j : U ⟶ X) [IsOpenImmersion j]

/-- The genuine restriction of regular functions to the chosen open,
viewed as an O_X-module map into its direct image. -/
@[expose] def unitMap : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction j).homEquiv _ _ (Scheme.Modules.restrictUnitIso j).hom

lemma unitMap_app (V : X.Opens) (a : Γ(X,V)) : (unitMap j).app V a = j.app V a := by
  change (j.appIso (j ⁻¹ᵁ V)).hom
    (X.presheaf.map (homOfLE (j.image_preimage_le V)).op a) = j.app V a
  have he := congrArg (fun f => f a) (j.app_appIso_inv V)
  calc
    _ = (j.appIso (j ⁻¹ᵁ V)).hom ((j.appIso (j ⁻¹ᵁ V)).inv (j.app V a)) :=
      congrArg (j.appIso (j ⁻¹ᵁ V)).hom he.symm
    _ = _ := Iso.inv_hom_id_apply _ _

/-- Injectivity is proved on ALL open sets. Empty opens have zero section
rings; nonempty opens meet the chosen nonempty open by irreducibility,
and restriction of regular functions on an integral scheme is injective. -/
lemma app_injective [IsIntegral X] [Nonempty U] (V : X.Opens) :
    Function.Injective (j.app V) := by
  rcases (V : Set X).eq_empty_or_nonempty with hV | hV
  · have h : V = ⊥ := SetLike.ext' hV
    subst V
    intro a b hab
    exact Subsingleton.elim _ _
  · have hU : (Set.range j).Nonempty := ⟨j (Classical.choice inferInstance),Set.mem_range_self _⟩
    obtain ⟨x,⟨u,rfl⟩,hu⟩ := nonempty_preirreducible_inter
      j.isOpenEmbedding.isOpen_range V.isOpen hU hV
    letI : Nonempty (j ''ᵁ (j ⁻¹ᵁ V)) := ⟨⟨j u,⟨u,hu,rfl⟩⟩⟩
    intro a b hab
    apply map_injective_of_isIntegral X (homOfLE (j.image_preimage_le V))
    have he := congrArg (fun z => (j.appIso (j ⁻¹ᵁ V)).inv z) hab
    have hmap := j.app_appIso_inv V
    simpa only [←ConcreteCategory.comp_apply,hmap] using he

/-- The structure sheaf embeds in the genuine open direct-image sheaf;
no normality or alleged sectionwise exactness is required. -/
instance unitMap_mono [IsIntegral X] [Nonempty U] : Mono (unitMap j) where
  right_cancellation := by
    intro M f g h
    apply Scheme.Modules.hom_ext
    intro V
    ext x
    apply app_injective j V
    have he := congrArg (fun φ => φ.app V x) h
    simpa only [Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,unitMap_app] using he
end IntegralOpenUnitMonomorphism318
