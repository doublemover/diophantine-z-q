module
public import UnitFrameSectionDetection318
public import ModuleGlobalSections318
public section
noncomputable section
namespace LocalFrameSectionDetection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y:Scheme.{u}} (M:X.Modules) (j:Y⟶X) [IsOpenImmersion j]
  [IsIntegral Y] (e:M.restrict j≅SheafOfModules.unit Y.ringCatSheaf)

include e

theorem image_injective (V:Y.Opens) [Nonempty V]:Function.Injective
    (M.presheaf.map (homOfLE (Scheme.Hom.image_mono j (show V≤⊤ from le_top))).op):=by
  exact UnitFrameSectionDetection318.restrict_injective e V ⊤ le_top

theorem chart_eq (V:Y.Opens) [Nonempty V] (W:X.Opens) (hw:j ''ᵁ V=W)
    (s t:Γ(M,⊤))
    (h:M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op s=
      M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op t):
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op t:=by
  subst W
  apply image_injective M j e V
  exact (CategoryTheory.Functor.map_comp_apply M.presheaf
    (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
    (homOfLE (Scheme.Hom.image_mono j (show V≤⊤ from le_top))).op s).symm.trans
      (h.trans (CategoryTheory.Functor.map_comp_apply M.presheaf
        (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (homOfLE (Scheme.Hom.image_mono j (show V≤⊤ from le_top))).op t))
end LocalFrameSectionDetection318
