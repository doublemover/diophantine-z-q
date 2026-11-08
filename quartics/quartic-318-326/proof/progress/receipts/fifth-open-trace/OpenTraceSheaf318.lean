module
public import OpenDominantTrace318
public import Mathlib.Algebra.Category.Ring.Basic
public section
noncomputable section
namespace OpenTraceSheaf318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 350000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
    (hfinite:letI:=AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
@[expose] def source:(Y.Opens)ᵒᵖ⥤AddCommGrpCat.{u}:=
  (Opens.map f.base).op ⋙ X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
@[expose] def target:(Y.Opens)ᵒᵖ⥤AddCommGrpCat.{u}:=
  Y.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
/-- The actual natural morphism of underlying additive section sheaves.
Its component over U is the previously constructed whole-open trace. -/
@[expose] def transfer:source f⟶target (Y:=Y) where
  app U:=AddCommGrpCat.ofHom (OpenDominantTrace318.trace f hY hfinite U.unop)
  naturality U V i:=by
    ext s
    exact (OpenDominantTrace318.restrict f hY hfinite i.unop s).symm
@[simp] lemma component (U:Y.Opens) (s:Γ(X,f⁻¹ᵁU)):
    (transfer f hY hfinite).app (Opposite.op U) s=
      OpenDominantTrace318.trace f hY hfinite U s:=rfl
/-- Scalar compatibility uses the exact original section pullback, giving
O_Y-linearity rather than only additivity of a family of functions. -/
lemma scalar (U:Y.Opens) (a:Γ(Y,U)) (s:Γ(X,f⁻¹ᵁU)):
    (transfer f hY hfinite).app (Opposite.op U) (f.app U a*s)=
      a*OpenDominantTrace318.trace f hY hfinite U s:=
  OpenDominantTrace318.linearity f hY hfinite U a s
end OpenTraceSheaf318
