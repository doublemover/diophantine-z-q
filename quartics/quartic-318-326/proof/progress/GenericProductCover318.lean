module
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace GenericProductCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y S : Scheme.{u}}
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- The actual relative product of two open covers, with the relative products
of chart schemes as its components. -/
@[expose] def cover (U:X.OpenCover) (V:Y.OpenCover) (f:X ⟶ S) (g:Y ⟶ S) :
    (pullback f g).OpenCover :=
  (U.pullbackCoverOfLeft f g).bind fun i=>V.pullbackCoverOfRight (U.f i ≫ f) g
@[simp] theorem obj (U:X.OpenCover) (V:Y.OpenCover) (f:X ⟶ S) (g:Y ⟶ S)
    (i:U.I₀) (j:V.I₀) : (cover U V f g).X ⟨i,j⟩=pullback (U.f i ≫ f) (V.f j ≫ g) := rfl
@[reassoc] theorem fst (U:X.OpenCover) (V:Y.OpenCover) (f:X ⟶ S) (g:Y ⟶ S)
    (i:U.I₀) (j:V.I₀) :
    (cover U V f g).f ⟨i,j⟩ ≫ pullback.fst f g=pullback.fst _ _ ≫ U.f i := by
  simp [cover,Precoverage.ZeroHypercover.bind,PreZeroHypercover.bind,
    Precoverage.ZeroHypercover.pullbackCoverOfLeft,PreZeroHypercover.pullbackCoverOfLeft,
    Precoverage.ZeroHypercover.pullbackCoverOfRight,PreZeroHypercover.pullbackCoverOfRight,Category.assoc]
@[reassoc] theorem snd (U:X.OpenCover) (V:Y.OpenCover) (f:X ⟶ S) (g:Y ⟶ S)
    (i:U.I₀) (j:V.I₀) :
    (cover U V f g).f ⟨i,j⟩ ≫ pullback.snd f g=pullback.snd _ _ ≫ V.f j := by
  simp [cover,Precoverage.ZeroHypercover.bind,PreZeroHypercover.bind,
    Precoverage.ZeroHypercover.pullbackCoverOfLeft,PreZeroHypercover.pullbackCoverOfLeft,
    Precoverage.ZeroHypercover.pullbackCoverOfRight,PreZeroHypercover.pullbackCoverOfRight,Category.assoc]
end GenericProductCover318
