module
public import RankOneTargetNeighborhood318
public import FifthChartNorm318
public section
noncomputable section
namespace FifthRankOneModuleNeighborhood318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
abbrev TargetRing (b:Bool):=Γ(Target,chartOpen b)
abbrev SourceRing (b:Bool):=Γ(Model,map⁻¹ᵁchartOpen b)
@[expose,instance_reducible] def sectionAlgebra (b:Bool):Algebra (TargetRing b) (SourceRing b):=
  (map.app (chartOpen b)).hom.toAlgebra
attribute [local instance] sectionAlgebra
lemma finite (b:Bool):Module.Finite (TargetRing b) (SourceRing b):=
  map.finite_app (chartOpen b) (chart_affine b)
lemma original_preimage (b:Bool) (a:TargetRing b):
    map⁻¹ᵁTarget.basicOpen a=Model.basicOpen (map.app (chartOpen b) a):=
  map.preimage_basicOpen a
variable (b:Bool) (L:Type*) [AddCommGroup L] [Module (SourceRing b) L]
  [Module.FinitePresentation (SourceRing b) L] [Module.Flat (SourceRing b) L]
  (rk:∀q:PrimeSpectrum (SourceRing b),Module.rankAtStalk L q=1)
include rk in
/-- Every point of either actual whole target chart has a principal
neighborhood whose entire inverse image trivializes this given finite-
presentation flat rank-one module on the original source section algebra.
No equivalence from arbitrary source line sheaves is assumed here. -/
lemma exists_basis (x:chartOpen b):
    ∃a:TargetRing b,x.1∈Target.basicOpen a ∧ Nonempty
      (Module.Basis (Fin 1) (Localization.Away (map.app (chartOpen b) a))
        (LocalizedModule.Away (map.app (chartOpen b) a) L)):=by
  letI:=finite b
  let p:PrimeSpectrum (TargetRing b):=(chart_affine b).primeIdealOf x
  obtain ⟨a,ha,hbasis⟩:=RankOneTargetNeighborhood318.exists_basis
    (TargetRing b) (SourceRing b) L rk p
  refine ⟨a,?_,hbasis⟩
  have hp:(chart_affine b).fromSpec p∈Target.basicOpen a:=by
    change p∈(chart_affine b).fromSpec⁻¹ᵁTarget.basicOpen a
    rw [(chart_affine b).fromSpec_preimage_basicOpen a]
    exact ha
  simpa only [p,IsAffineOpen.fromSpec_primeIdealOf] using hp
end FifthRankOneModuleNeighborhood318
