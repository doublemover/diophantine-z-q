module
public import IdentityCotangent318
public section
noncomputable section
namespace PullbackLineFrames318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y U V : Scheme.{u}} (p : X ⟶ Y)
    (j : U ⟶ Y) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (g : V ⟶ U) (h : k≫p=g≫j) (L : Y.Modules)

/-- Exact change of chart for the actual pullback functor, retaining the
specified commuting square. It requires no flatness assumption. -/
@[expose] def chartIso : ((Scheme.Modules.pullback p).obj L).restrict k ≅
    (Scheme.Modules.pullback g).obj (L.restrict j) :=
  (Scheme.Modules.restrictFunctorIsoPullback k).app ((Scheme.Modules.pullback p).obj L) ≪≫
    (Scheme.Modules.pullbackComp k p).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    ((Scheme.Modules.pullbackComp g j).app L).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app L).symm

/-- An actual chart frame pulls back to an actual chart frame, using the
canonical pullback-of-unit comparison. -/
@[expose] def frame (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) :
    ((Scheme.Modules.pullback p).obj L).restrict k ≅ SheafOfModules.unit V.ringCatSheaf :=
  chartIso p j k g h L ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
    IdentityCotangent318.pullbackUnitIso g
end PullbackLineFrames318
