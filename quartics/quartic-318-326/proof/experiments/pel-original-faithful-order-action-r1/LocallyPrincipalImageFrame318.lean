module
public import OpenRestrictionImages318
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public section
noncomputable section
namespace LocallyPrincipalImageFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
variable {M N : Y.Modules} (f : M ⟶ N)
variable (b : (Scheme.Modules.restrictFunctor j).obj M ⟶
    SheafOfModules.unit X.ringCatSheaf)
variable (a : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor j).obj N)
variable (h : b ≫ a = (Scheme.Modules.restrictFunctor j).map f) [Epi b] [Mono a]

/-- An actual split-surjective local coefficient row and an injective
rational generator identify the restriction of the whole image sheaf
with the structure sheaf. The image is not computed sectionwise. -/
@[expose] def frame : SheafOfModules.unit X.ringCatSheaf ≅
    (Scheme.Modules.restrictFunctor j).obj (image f) :=
  image.isoStrongEpiMono b a h ≪≫ OpenRestrictionImages318.imageIso j f

@[reassoc] lemma frame_inclusion :
    (frame j f b a h).hom ≫ (Scheme.Modules.restrictFunctor j).map (image.ι f) = a := by
  rw [frame,Iso.trans_hom,Category.assoc,OpenRestrictionImages318.imageIso_inclusion,
    image.isoStrongEpiMono_hom_comp_ι]

@[reassoc] lemma coefficient_row :
    b ≫ (frame j f b a h).hom =
      (Scheme.Modules.restrictFunctor j).map (factorThruImage f) := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctor j).map (image.ι f))).1
  rw [Category.assoc,frame_inclusion,h,←Functor.map_comp,image.fac]

/-- A local generator comparison determines the entire transition map,
using the genuine monomorphism into the common rational sheaf. -/
lemma transition {b' : (Scheme.Modules.restrictFunctor j).obj M ⟶
      SheafOfModules.unit X.ringCatSheaf}
    {a' : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.restrictFunctor j).obj N}
    (h' : b' ≫ a' = (Scheme.Modules.restrictFunctor j).map f)
    [Epi b'] [Mono a']
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hu : u ≫ a' = a) :
    (frame j f b a h).hom ≫ (frame j f b' a' h').inv = u := by
  apply (cancel_mono a').1
  have hi : (frame j f b' a' h').inv ≫ a' =
      (Scheme.Modules.restrictFunctor j).map (image.ι f) := by
    rw [←frame_inclusion j f b' a' h',Iso.inv_hom_id_assoc]
  rw [Category.assoc,hi,frame_inclusion,hu]
end LocallyPrincipalImageFrame318
