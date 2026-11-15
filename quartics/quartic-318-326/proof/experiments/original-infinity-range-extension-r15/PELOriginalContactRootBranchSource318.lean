module
public import PELOriginalContactRootHolomorphy318
public import PELOriginalContactParameterLocality318
public import FourRootPuncturedRegularity318
public section
noncomputable section
namespace PELOriginalContactRootBranchSource318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalContactBranchParameters318 PELOriginalContactParameterLocality318
open FourCharacterRootRecombination318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold

lemma regular_of_projection (x:UnlevelledBase) (t:ℂ)
    (h:normalizedMap x=(t:OnePoint ℂ)) (hd:denominator branches t≠0):
    x∈RegularSource ∧ base x=t := by
  have hb:PELOriginalMaximalQuotient318.projection x=basePoint t:=
    PELOriginalManuscriptNormalization318.coordinate.injective
      (h.trans (basePoint_value t).symm)
  refine ⟨?_,base_at t x hb⟩
  change PELOriginalMaximalQuotient318.projection x∉PELStabilizerLocusInvariant318.branchImage
  rw [hb]
  exact (PELOriginalCommonContactBase318.regular_iff t).mpr hd

lemma source_holomorphic {p:UnlevelledBase} {B:ℂ→OnePoint ℂ}
    (P:SquareParametrization p B):
    ∀ᶠw in 𝓝 (0:ℂ),ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (source P) w := by
  filter_upwards [P.projection,P.inverse_analytic.eventually_analyticAt] with w hw ha
  exact (P.chart_inverse_holomorphic _ hw.1).comp w
    (contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt)

lemma finite_regular {p:UnlevelledBase} (j:Fin 4)
    (P:SquareParametrization p (fun w=>(branches j+w^2:ℂ))):
    ∀ᶠw in 𝓝[≠] (0:ℂ),source P w∈RegularSource ∧ base (source P w)=branches j+w^2 := by
  filter_upwards [P.projection.filter_mono nhdsWithin_le_nhds,
    FourRootPuncturedRegularity318.finite branches branches_injective j] with w hp hd
  exact regular_of_projection _ _ hp.2 hd

lemma infinity_regular {p:UnlevelledBase}
    (P:SquareParametrization p (fun w=>SphereInversion318.inversion (w^2:ℂ))):
    ∀ᶠw in 𝓝[≠] (0:ℂ),source P w∈RegularSource ∧ base (source P w)=(w^2)⁻¹ := by
  filter_upwards [P.projection.filter_mono nhdsWithin_le_nhds,
    FourRootPuncturedRegularity318.infinity branches,self_mem_nhdsWithin] with w hp hd hn
  have h:normalizedMap (source P w)=((w^2)⁻¹:ℂ):=by
    rw [hp.2,SphereInversion318.inversion_coe (pow_ne_zero 2 hn)]
  exact regular_of_projection _ _ h hd

/-- The original root functions, composed with the actual original local
parameter, are punctured holomorphic. The domain is derived, not supplied
as a replacement punctured sheet. -/
lemma roots_differentiable {p:UnlevelledBase} {B:ℂ→OnePoint ℂ}
    (P:SquareParametrization p B)
    (hr:∀ᶠw in 𝓝[≠] (0:ℂ),source P w∈RegularSource) (k:Fin 4):
    ∀ᶠw in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ (fun v=>roots (source P v) k) w := by
  filter_upwards [hr,(source_holomorphic P).filter_mono nhdsWithin_le_nhds] with w hw hs
  have hh:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun v=>roots (source P v) k) w:=
    (PELOriginalContactRootHolomorphy318.roots_holomorphic _ hw k).comp w hs
  exact (contMDiffAt_iff_contDiffAt.mp hh).differentiableAt (by simp)

lemma finite_equation {p:UnlevelledBase} (j:Fin 4)
    (P:SquareParametrization p (fun w=>(branches j+w^2:ℂ))) (k:Fin 4):
    ∀ᶠw in 𝓝[≠] (0:ℂ),roots (source P w) k^2=branches j-branches k+w^2 := by
  filter_upwards [finite_regular j P] with w hw
  rw [roots_square _ hw.1 k,hw.2]
  ring
lemma infinity_equation {p:UnlevelledBase}
    (P:SquareParametrization p (fun w=>SphereInversion318.inversion (w^2:ℂ))) (k:Fin 4):
    ∀ᶠw in 𝓝[≠] (0:ℂ),roots (source P w) k^2=(w^2)⁻¹-branches k := by
  filter_upwards [infinity_regular P] with w hw
  rw [roots_square _ hw.1 k,hw.2]
end PELOriginalContactRootBranchSource318
