module
public import PullbackChartNaturality318
public import ModuleTopMorphisms318
public section
noncomputable section
namespace PulledCoordinateMaps318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
abbrev unit (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
variable {X Y U V : Scheme.{u}} (p : X ⟶ Y)
    {L : Y.Modules} (f : unit Y ⟶ L)
/-- Canonical pulled section morphism, including the pullback-of-unit comparison. -/
@[expose] def map : unit X ⟶ (Scheme.Modules.pullback p).obj L :=
  (IdentityCotangent318.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map f
@[expose] def sectionTop : Γ((Scheme.Modules.pullback p).obj L,⊤) :=
  (map p f).app ⊤ (show Γ(X,⊤) from 1)

variable (j : U ⟶ Y) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (g : V ⟶ U) (h : k≫p=g≫j)
include g h in
/-- A coordinate which generates on a target chart generates on every source
chart factoring through it, for the literal pulled coordinate map. -/
theorem restrict_isIso [IsIso ((Scheme.Modules.restrictFunctor j).map f)] :
    IsIso ((Scheme.Modules.restrictFunctor k).map (map p f)) := by
  letI := PullbackChartNaturality318.restricted_map_isIso p j k g h f
  unfold map
  rw [Functor.map_comp]
  infer_instance
end PulledCoordinateMaps318
