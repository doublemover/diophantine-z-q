module
public import LineFrameTopScalar318
public import ModuleGlobalSections318
public section
noncomputable section
namespace OriginalOpenTopSection318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal original section on U, regarded as a top section on the
actual open subscheme. The only transport is the canonical image equality. -/
@[expose] def top (s : Γ(M,U)) : Γ(M.restrict U.ι,⊤) :=
  M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U)).op s

lemma image_le (V : U.toScheme.Opens) : U.ι ''ᵁ V ≤ U := by
  simpa using U.ι.image_le_opensRange V

/-- Restricting the actual top section is exactly restricting the original
section to the image open. This fixes the map on every subopen, not only points. -/
lemma restrict_top (s : Γ(M,U)) (V : U.toScheme.Opens) :
    (M.restrictAppIso U.ι V).hom
      ((M.restrict U.ι).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
        (top M U s)) =
    M.presheaf.map (homOfLE (image_le U V)).op s := by
  change M.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι (show V≤⊤ from le_top))).op
    (M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U)).op s) = _
  rw [← ConcreteCategory.comp_apply,← Functor.map_comp]
  congr 2

@[expose] def map (s : Γ(M,U)) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι :=
  ModuleGlobalSections318.ofTop (M.restrict U.ι) (top M U s)

lemma map_formula (s : Γ(M,U)) (V : U.toScheme.Opens) (a : Γ(U.toScheme,V)) :
    (M.restrictAppIso U.ι V).hom ((map M U s).app V a) =
      (U.ι.appIso V).inv a • M.presheaf.map (homOfLE (image_le U V)).op s := by
  rw [map,ModuleGlobalSections318.ofTop_apply]
  change (U.ι.appIso V).inv a •
    (M.restrictAppIso U.ι V).hom
      ((M.restrict U.ι).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
        (top M U s)) = _
  rw [restrict_top]
end OriginalOpenTopSection318
