module
public import OpenDominantNorm318
public import Mathlib.Algebra.Category.Grp.Basic
public section
noncomputable section
namespace OpenUnitNorm318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- The actual group of units of each commutative ring, with its original maps. -/
@[expose] def unitsFunctor:CommRingCat.{u}⥤CommGrpCat.{u} where
  obj R:=CommGrpCat.of Rˣ
  map f:=CommGrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id _:=CommGrpCat.ext fun _=>Units.ext rfl
  map_comp _ _:=CommGrpCat.ext fun _=>Units.ext rfl
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
@[expose] def targetUnits:Y.Opensᵒᵖ⥤CommGrpCat:=Y.presheaf⋙unitsFunctor
@[expose] def sourceUnits:Y.Opensᵒᵖ⥤CommGrpCat:=(f.base _* X.presheaf)⋙unitsFunctor
/-- A genuine natural transformation on units of regular functions, including
arbitrary disconnected and empty opens. -/
@[expose] def norm:sourceUnits f⟶targetUnits (Y:=Y) where
  app U:=CommGrpCat.ofHom (Units.map (OpenDominantNorm318.norm f hY U.unop))
  naturality U V i:=by
    apply CommGrpCat.ext
    intro s
    change Γ(X,f⁻¹ᵁU.unop)ˣ at s
    apply Units.ext
    exact (OpenDominantNorm318.restrict f hY i.unop (s:Γ(X,f⁻¹ᵁU.unop))).symm
lemma value (U:Y.Opens) (s:Γ(X,f⁻¹ᵁU)ˣ):
    Units.val (α:=Γ(Y,U)) ((norm f hY).app (op U) s)=OpenDominantNorm318.norm f hY U (s:Γ(X,f⁻¹ᵁU)):=rfl
lemma pullback (U:Y.Opens) (s:Γ(Y,U)ˣ):
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    (norm f hY).app (op U) (Units.map (f.app U).hom.toMonoidHom s)=
      s^Module.finrank Y.functionField X.functionField:=by
  apply Units.ext
  exact OpenDominantNorm318.pullback f hY U (s:Γ(Y,U))
end OpenUnitNorm318
