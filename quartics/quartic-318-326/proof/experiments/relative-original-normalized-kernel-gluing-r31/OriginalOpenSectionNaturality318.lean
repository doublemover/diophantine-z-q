module
public import OriginalSectionTransport318
public import OriginalSectionPullbackComposition318
public section
noncomputable section
namespace OriginalOpenSectionNaturality318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalSectionTransport318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

/-- Restriction of the genuine global pullback unit agrees with the unit on the
whole inverse-image open, retaining the proved open equality. -/
lemma restrict_top (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U=V) (s : Γ(M,⊤)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (homOfLE (show V≤⊤ from le_top)).op (OriginalSectionPullbackComposition318.pull f M s) =
    pullTo f M U V h (M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op s) := by
  subst V
  have hn := congrArg (fun q => q s)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      (homOfLE (show U≤⊤ from le_top)).op)
  simpa only [pullTo,move,eqToHom_refl,op_id,Functor.map_id,ConcreteCategory.id_apply,
    AddMonoidHom.comp_apply,OriginalSectionPullbackComposition318.pull] using hn.symm

lemma pullTo_map {N : Y.Modules} (a : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U=V) (s : Γ(M,U)) :
    ((Scheme.Modules.pullback f).map a).app V (pullTo f M U V h s)=
      pullTo f N U V h (a.app U s) := by
  subst V
  have hn := congrArg (fun q => q.app U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)
  simpa only [pullTo,move,eqToHom_refl,op_id,Functor.map_id,ConcreteCategory.id_apply,
    AddMonoidHom.comp_apply] using hn.symm
end OriginalOpenSectionNaturality318
