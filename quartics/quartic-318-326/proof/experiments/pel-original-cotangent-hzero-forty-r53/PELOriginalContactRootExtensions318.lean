module
public import PELOriginalContactRootBranchSource318
public import FourRootFiniteBranchExtension318
public import FourRootInfinityExtension318
public section
noncomputable section
namespace PELOriginalContactRootExtensions318
open Set Filter
open scoped Topology OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalContactBranchParameters318 PELOriginalContactParameterLocality318
open PELOriginalContactRootBranchSource318
open PELOriginalBranchLabels318

@[expose] def finiteParameter (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)):=
  PELOriginalContactBranchParameters318.finite p hp (branches j) h
@[expose] def infinityParameter (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞):=
  PELOriginalContactBranchParameters318.infinity p hp h

/-- Every actual finite original ramification point receives all four
extended coordinates from the SAME original generic map. Only its jth
root vanishes, and that root is a genuine local parameter. -/
theorem finite (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) :
    ∃Z:Fin 4→ℂ→ℂ,∃inv:ℂ→ℂ,
      (∀k,AnalyticAt ℂ (Z k) 0) ∧
      (∀k,Z k=ᶠ[𝓝[≠] (0:ℂ)] (fun w=>roots (source (finiteParameter p hp j h) w) k)) ∧
      (∀k,(Z k 0)^2=branches j-branches k) ∧ Z j 0=0 ∧
      (∀k,k≠j→Z k 0≠0) ∧ deriv (Z j) 0^2=1 ∧
      AnalyticAt ℂ inv 0 ∧ inv 0=0 ∧
      (fun w=>inv (Z j w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>Z j (inv w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠw in 𝓝 (0:ℂ),∀k,(Z k w)^2=branches j-branches k+w^2) := by
  let P:=finiteParameter p hp j h
  exact FourRootFiniteBranchExtension318.extend branches branches_injective j
    (fun k w=>roots (source P w) k)
    (fun k=>roots_differentiable P ((finite_regular j P).mono fun _ hw=>hw.1) k)
    (finite_equation j P)

/-- Every actual original infinity point retains its three normalized
sign ratios. The constructed local parameter is exactly1/z0 on the
punctured original map, with derivative squared1, not a collapsed
character-fiber-product point. -/
theorem infinity (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞) :
    ∃r:Fin 4→ℂ→ℂ,∃inv:ℂ→ℂ,
      (∀k,AnalyticAt ℂ (r k) 0) ∧ (∀k,(r k 0)^2=1) ∧
      (∀k,r k=ᶠ[𝓝[≠] (0:ℂ)] (fun w=>w*roots (source (infinityParameter p hp h) w) k)) ∧
      AnalyticAt ℂ (FourRootInfinityExtension318.parameter r) 0 ∧ FourRootInfinityExtension318.parameter r 0=0 ∧
      deriv (FourRootInfinityExtension318.parameter r) 0^2=1 ∧
      AnalyticAt ℂ inv 0 ∧ inv 0=0 ∧
      (fun w=>inv (FourRootInfinityExtension318.parameter r w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>FourRootInfinityExtension318.parameter r (inv w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀k,AnalyticAt ℂ (FourRootInfinityExtension318.ratio r k) 0 ∧ (FourRootInfinityExtension318.ratio r k 0)^2=1) ∧
      (∀ᶠw in 𝓝 (0:ℂ),FourRootInfinityExtension318.ratio r 0 w=1 ∧
        ∀k,(FourRootInfinityExtension318.ratio r k w)^2=1+(branches 0-branches k)*(FourRootInfinityExtension318.parameter r w)^2) ∧
      (∀ᶠw in 𝓝[≠] (0:ℂ),FourRootInfinityExtension318.parameter r w=(roots (source (infinityParameter p hp h) w) 0)⁻¹ ∧
        ∀k,FourRootInfinityExtension318.ratio r k w=roots (source (infinityParameter p hp h) w) k/roots (source (infinityParameter p hp h) w) 0) := by
  let P:=infinityParameter p hp h
  exact FourRootInfinityExtension318.extend branches
    (fun k w=>roots (source P w) k)
    (fun k=>roots_differentiable P ((infinity_regular P).mono fun _ hw=>hw.1) k)
    (infinity_equation P)
end PELOriginalContactRootExtensions318
