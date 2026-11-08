module
public import FifthPushforwardModules318
public import AffinePrincipalBasis318
public import FifthTargetNormalBasis318
public section
noncomputable section
namespace FifthPrincipalNeighborhood318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
attribute [local instance] AffinePrincipalBasis318.originalAlgebra AffinePrincipalBasis318.localAlgebra
/-- At each specified point of either original chart, a genuine principal
neighborhood has a rank-eight basis of sections on its entire inverse image. -/
lemma exists_basis (b:Bool) (x:chartOpen b):
    ∃r:Γ(Target,chartOpen b),x.1∈Target.basicOpen r ∧ Nonempty
      (Module.Basis (Fin 8) Γ(Target,Target.basicOpen r) Γ(Model,map⁻¹ᵁTarget.basicOpen r)):=by
  let p:PrimeSpectrum Γ(Target,chartOpen b):=(chart_affine b).primeIdealOf x
  obtain ⟨r,hr,⟨bs⟩⟩:=FifthPushforwardModules318.exists_principal_basis b p
  refine ⟨r,?_,⟨AffinePrincipalBasis318.basis map (chartOpen b) r
    (chart_affine b) ((chart_affine b).preimage map) bs⟩⟩
  have hp:(chart_affine b).fromSpec p∈Target.basicOpen r:=by
    change p∈(chart_affine b).fromSpec⁻¹ᵁTarget.basicOpen r
    rw [(chart_affine b).fromSpec_preimage_basicOpen r]
    exact hr
  simpa only [p,IsAffineOpen.fromSpec_primeIdealOf] using hp
/-- These genuine finite-free rank-eight neighborhoods cover the whole
completed target, including the elliptic zero and all branch values. -/
lemma cover (x:Target):
    ∃(b:Bool)(r:Γ(Target,chartOpen b)),x∈Target.basicOpen r ∧ Nonempty
      (Module.Basis (Fin 8) Γ(Target,Target.basicOpen r) Γ(Model,map⁻¹ᵁTarget.basicOpen r)):=by
  obtain ⟨b,hb⟩:=FifthTargetNormalBasis318.chart_cover x
  obtain ⟨r,hr,hbasis⟩:=exists_basis b ⟨x,hb⟩
  exact ⟨b,r,hr,hbasis⟩
end FifthPrincipalNeighborhood318
