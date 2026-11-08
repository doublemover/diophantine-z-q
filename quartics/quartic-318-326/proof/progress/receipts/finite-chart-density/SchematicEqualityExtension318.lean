module
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace SchematicEqualityExtension318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality after a schematically dominant map into a separated relative
target implies equality, without assuming the source is reduced. -/
theorem ext {W X Y Z:Scheme} {f g:X⟶Y} (s:Y⟶Z) [IsSeparated s]
    (h:f≫s=g≫s) (i:W⟶X) [IsSchemeTheoreticallyDominant i]
    (hi:i≫f=i≫g) : f=g:=by
  let X':Over Z:=Over.mk (f≫s)
  let Y':Over Z:=Over.mk s
  let W':Over Z:=Over.mk (i≫f≫s)
  let f':X'⟶Y':=Over.homMk f
  let g':X'⟶Y':=Over.homMk g
  let i':W'⟶X':=Over.homMk i
  have he:i'≫f'=i'≫g':=by ext1;exact hi
  haveI:IsSeparated Y'.hom:=inferInstanceAs (IsSeparated s)
  have hk:(equalizer.ι f' g').left.ker=⊥:=by
    apply le_antisymm ?_ bot_le
    calc
      (equalizer.ι f' g').left.ker≤
        ((equalizer.lift i' he).left≫(equalizer.ι f' g').left).ker:=Scheme.Hom.le_ker_comp _ _
      _=i.ker:=by rw [←Over.comp_left,equalizer.lift_ι];rfl
      _=⊥:=i.ker_eq_bot
  haveI:IsIso (equalizer.ι f' g').left:=IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [←cancel_epi (equalizer.ι f' g').left]
  congrm $(equalizer.condition f' g').left
end SchematicEqualityExtension318
