module
public import ModuleTopExt318
public import ClutchedModule318
public section
noncomputable section
namespace NormalizedSectionFrame318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (e : M.restrict j ≅ ClutchedModule318.unit Y)
    (f : ClutchedModule318.unit X ⟶ M)

/-- The literal local coordinate map, using canonical restriction of the unit. -/
@[expose] def framedMap : ClutchedModule318.unit Y ⟶ ClutchedModule318.unit Y :=
  (Scheme.Modules.restrictUnitIso j).inv ≫ (Scheme.Modules.restrictFunctor j).map f ≫ e.hom

theorem framedMap_top_one :
    (framedMap j M e f).app ⊤ (show Γ(Y,⊤) from 1)=
      e.hom.app ⊤ (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (f.app ⊤ (show Γ(X,⊤) from 1))) := by
  have hu : (Scheme.Modules.restrictUnitIso j).inv.app ⊤
      (show Γ(Y,⊤) from 1)=(show Γ(X,j ''ᵁ ⊤) from 1) := by
    change (j.appIso ⊤).inv.hom 1=1
    exact map_one _
  change e.hom.app ⊤ (f.app (j ''ᵁ ⊤)
    ((Scheme.Modules.restrictUnitIso j).inv.app ⊤ (show Γ(Y,⊤) from 1)))=_
  rw [hu]
  congr 1
  have hn := congrArg (fun g => g (show Γ(X,⊤) from 1))
    (f.mapPresheaf.naturality (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op)
  change f.app (j ''ᵁ ⊤) (X.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op 1)=
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f.app ⊤ (show Γ(X,⊤) from 1)) at hn
  simpa only [map_one] using hn

/-- An exact top-open frame value determines the entire framed sheaf map. -/
theorem framedMap_eq (a : Γ(Y,⊤))
    (ha : e.hom.app ⊤ (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f.app ⊤ (show Γ(X,⊤) from 1)))=a) :
    framedMap j M e f=ClutchedModule318.multiply a := by
  apply ModuleTopExt318.ext
  exact (framedMap_top_one j M e f).trans (ha.trans (by simpa only [one_mul] using (ClutchedModule318.multiply_top a 1).symm))

/-- A unit frame value proves the whole restricted coordinate map is an isomorphism. -/
theorem restrict_isIso (a : Γ(Y,⊤)) (ha : IsUnit a)
    (hf : e.hom.app ⊤ (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f.app ⊤ (show Γ(X,⊤) from 1)))=a) :
    IsIso ((Scheme.Modules.restrictFunctor j).map f) := by
  have he := framedMap_eq j M e f a hf
  haveI : IsIso (framedMap j M e f) := he.symm ▸ ClutchedModule318.multiply_isIso a ha
  have hh : (Scheme.Modules.restrictFunctor j).map f=
      (Scheme.Modules.restrictUnitIso j).hom ≫ framedMap j M e f ≫ e.inv := by
    simp [framedMap]
  rw [hh]
  infer_instance
end NormalizedSectionFrame318
