module
public import ComplexLineLatticeMaps318
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public section
noncomputable section
namespace ComplexTorusCoverLift318
open Set Topology
open ComplexLineLatticeAtlas318
variable (L:AddSubgroup ℂ) [DiscreteTopology L]
variable {E:Type*} [TopologicalSpace E]
variable (p:E→Quotient L) (cov:IsCoveringMap p) (e₀:E) (he:p e₀=projection L 0)

/-- Lift the GENUINE complex-line projection through the specified actual
cover. No source uniformization, affine lift, period group or rank basis
is supplied. The source remains the original covering space E. -/
@[expose] def lift : C(ℂ,E):=
  (cov.existsUnique_continuousMap_lifts
    ⟨projection L,(quotient_covering L).isCoveringMap.continuous⟩ 0 e₀ he).choose
lemma lift_zero : lift L p cov e₀ he 0=e₀:=
  (cov.existsUnique_continuousMap_lifts
    ⟨projection L,(quotient_covering L).isCoveringMap.continuous⟩ 0 e₀ he).choose_spec.1.1
lemma lift_projection (z:ℂ) : p (lift L p cov e₀ he z)=projection L z:=
  congrFun (cov.existsUnique_continuousMap_lifts
    ⟨projection L,(quotient_covering L).isCoveringMap.continuous⟩ 0 e₀ he).choose_spec.1.2 z

/-- The lift is locally a genuine homeomorphism because both ORIGINAL
projections are local homeomorphisms and its continuity was constructed. -/
theorem lift_localHomeomorph : IsLocalHomeomorph (lift L p cov e₀ he) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hc:p ∘ lift L p cov e₀ he=projection L:=funext (lift_projection L p cov e₀ he)
  apply IsLocalHomeomorphOn.of_comp_left
    (show IsLocalHomeomorphOn (p ∘ lift L p cov e₀ he) univ from
      hc.symm ▸ (quotient_localHomeomorph L).isLocalHomeomorphOn)
    (cov.isLocalHomeomorph.isLocalHomeomorphOn)
  intro z _
  exact (lift L p cov e₀ he).continuous.continuousAt

/-- Path lifting through the EXISTING target torus projection proves
surjectivity onto the entire connected original cover. This is not
assumed from local surjectivity or from the number of covering sheets. -/
theorem lift_surjective [PathConnectedSpace E] : Function.Surjective (lift L p cov e₀ he) := by
  intro e
  let γ:=PathConnectedSpace.somePath e₀ e
  let δ:C(unitInterval,Quotient L):=⟨p ∘ γ,cov.continuous.comp γ.continuous⟩
  have hδ:δ 0=projection L 0:=by
    change p (γ 0)=projection L 0
    rw [γ.source,he]
  let c:=(quotient_covering L).isCoveringMap
  let Γ:=c.liftPath δ 0 hδ
  have hproj:p ∘ (lift L p cov e₀ he ∘ Γ)=p ∘ γ:=by
    funext t
    change p (lift L p cov e₀ he (Γ t))=p (γ t)
    rw [lift_projection]
    exact congrFun (c.liftPath_lifts δ 0 hδ) t
  have hstart:(lift L p cov e₀ he ∘ Γ) 0=γ 0:=by
    change lift L p cov e₀ he (Γ 0)=γ 0
    rw [show Γ 0=0 from c.liftPath_zero δ 0 hδ,lift_zero,γ.source]
  have hh:=cov.eq_of_comp_eq ((lift L p cov e₀ he).continuous.comp Γ.continuous)
    γ.continuous hproj 0 hstart
  exact ⟨Γ 1,(congrFun hh 1).trans γ.target⟩
end ComplexTorusCoverLift318
