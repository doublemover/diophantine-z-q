module
public import ComplexLineLatticeMaps318
public import OpenQuotientSameFibers318
public import ComplexCurveHomeomorphInverse318
public section
noncomputable section
namespace ComplexCoverQuotientBiholomorph318
open Set Filter Topology ComplexLineLatticeAtlas318
open scoped Manifold ContDiff
variable (Λ:AddSubgroup ℂ) [DiscreteTopology Λ]
variable {E:Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ,ℂ) ω E]
local instance : ChartedSpace ℂ (Quotient Λ):=chartedSpace Λ
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient Λ):=complex_manifold Λ
variable (F:C(ℂ,E)) (hlocal:IsLocalHomeomorph F) (hsur:Function.Surjective F)
  (hfiber:∀z w:ℂ,projection Λ z=projection Λ w ↔ F z=F w)

lemma projection_quotient : IsQuotientMap (projection Λ) :=
  (show IsOpenQuotientMap (projection Λ) from
    { continuous:=(quotient_covering Λ).isCoveringMap.continuous
      surjective:=quotient_surjective Λ
      isOpenMap:=(quotient_localHomeomorph Λ).isOpenMap }).isQuotientMap
lemma lift_quotient : IsQuotientMap F :=
  (show IsOpenQuotientMap F from {continuous:=F.continuous,surjective:=hsur,isOpenMap:=hlocal.isOpenMap}).isQuotientMap

/-- The quotient by the ACTUAL complete fiber relation is homeomorphic
to the unchanged original cover, via two genuine quotient maps. -/
@[expose] def comparison : Quotient Λ≃ₜE:=
  OpenQuotientSameFibers318.homeomorph (projection Λ) F
    (projection_quotient Λ) (lift_quotient F hlocal hsur) hfiber
lemma comparison_projection (z:ℂ) :
    comparison Λ F hlocal hsur hfiber (projection Λ z)=F z:=
  OpenQuotientSameFibers318.homeomorph_value (projection Λ) F
    (projection_quotient Λ) (lift_quotient F hlocal hsur) hfiber z

/-- Holomorphic descent uses the actual quotient charts, whose inverse
is the original projection. It does not transport the source complex
structure along the new point equivalence. -/
theorem comparison_holomorphic (hF:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison Λ F hlocal hsur hfiber) := by
  intro p
  obtain ⟨a,rfl⟩:=quotient_surjective Λ p
  let e:=localChart Λ a
  have hp:projection Λ a∈e.source:=localChart_center Λ a
  have hv:e (projection Λ a)=a:=(quotient_localHomeomorph Λ).localInverseAt_apply_self
  have hlocalF:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun z=>comparison Λ F hlocal hsur hfiber (e.symm z)) a := by
    apply (hF a).congr_of_eventuallyEq
    exact Eventually.of_forall (fun z=>by
      rw [show e.symm z=projection Λ z from localChart_symm Λ a z,comparison_projection])
  have hc:=contMDiffAt_of_mem_maximalAtlas (ComplexLineLatticeMaps318.chart_maximal Λ a) hp
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun z=>comparison Λ F hlocal hsur hfiber (e.symm z)) (e (projection Λ a)):=by
    rwa [hv]
  apply (hh.comp _ hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  change comparison Λ F hlocal hsur hfiber q=
    comparison Λ F hlocal hsur hfiber (e.symm (e q))
  rw [e.left_inv hq]
theorem comparison_biholomorphic (hF:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison Λ F hlocal hsur hfiber) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison Λ F hlocal hsur hfiber).symm :=
  ⟨comparison_holomorphic Λ F hlocal hsur hfiber hF,
    ComplexCurveHomeomorphInverse318.inverse _ (comparison_holomorphic Λ F hlocal hsur hfiber hF)⟩
end ComplexCoverQuotientBiholomorph318
