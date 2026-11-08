module
public import PushforwardStructureSheaf318
public import FifthOpenTrace318
public section
noncomputable section
namespace FifthPushforwardModule318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The actual rank-eight candidate, with its original pushforward structure. -/
abbrev object:Target.Modules:=PushforwardStructureSheaf318.object map
abbrev unit:Target.Modules:=SheafOfModules.unit Target.ringCatSheaf
@[expose] def pullbackLinear (U:Target.Opens):Γ(unit,U)→ₗ[Γ(Target,U)]Γ(object,U) where
  toFun:=map.app U
  map_add':=(map.app U).hom.map_add
  map_smul':=by
    intro a s
    change map.app U (a*(show Γ(Target,U) from s))=map.app U a*map.app U s
    exact (map.app U).hom.map_mul a s
@[expose] def traceLinear (U:Target.Opens):Γ(object,U)→ₗ[Γ(Target,U)]Γ(unit,U) where
  toFun:=FifthOpenTrace318.trace U
  map_add':=(FifthOpenTrace318.trace U).map_add
  map_smul':=by
    intro a s
    exact FifthOpenTrace318.linearity U a s
/-- The literal regular-function pullback, as an O_target-module morphism. -/
@[expose] def pullback:unit⟶object where
  val.app W:=ConcreteCategory.ofHom (C:=ModuleCat _) (pullbackLinear W.unop)
  val.naturality i:=by
    apply ModuleCat.hom_injective
    apply LinearMap.ext
    intro s
    exact congrArg (fun g=>g s) (map.naturality i)
/-- The existing all-open regular trace bundled as a genuine O_target-module
morphism, with the same actual section components. -/
@[expose] def trace:object⟶unit where
  val.app W:=ConcreteCategory.ofHom (C:=ModuleCat _) (traceLinear W.unop)
  val.naturality i:=by
    ext s
    exact (FifthOpenTrace318.restrict i.unop s).symm
@[simp] lemma pullback_component (U:Target.Opens) (s:Γ(Target,U)):
    pullback.app U s=map.app U s:=rfl
@[simp] lemma trace_component (U:Target.Opens) (s:Γ(object,U)):
    trace.app U s=FifthOpenTrace318.trace U s:=rfl
/-- Exact push-pull identity on every section of the original module sheaf,
not just its generic fiber. -/
lemma pullback_trace (U:Target.Opens) (s:Γ(unit,U)):
    (pullback≫trace).app U s=8*(show Γ(Target,U) from s):=
  FifthOpenTrace318.trace_pullback U s
end FifthPushforwardModule318
