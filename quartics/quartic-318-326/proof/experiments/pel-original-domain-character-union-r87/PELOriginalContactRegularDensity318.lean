module
public import PELOriginalCompletedContactGeneric318
public section
noncomputable section
namespace PELOriginalContactRegularDensity318
open Set Filter
open scoped Topology OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 PELOriginalContactRootExtensions318
open PELOriginalContactRootBranchSource318 PELOriginalContactParameterLocality318
open PELOriginalContactBranchParameters318

lemma regular_open : IsOpen RegularSource:=
  PELOriginalFiniteBranchImage318.original_branch_image_finite.isClosed.isOpen_compl.preimage
    PELOriginalMaximalQuotient318.projection_continuous

/-- Actual branch parameters approach EVERY original branch point from
the true full regular locus. Density is not inferred from a genus count
or from a replacement curve. -/
lemma closure_from_parameter {p:UnlevelledBase} {B:ℂ→OnePoint ℂ}
    (P:SquareParametrization p B)
    (hr:∀ᶠw in 𝓝[≠] (0:ℂ),source P w∈RegularSource) : p∈closure RegularSource := by
  have h0:(0:ℂ)∈P.chart.target:=by
    rw [←P.center_zero]
    exact P.chart.map_source P.center_mem
  have hc:ContinuousAt (source P) 0:=by
    have hi:ContinuousAt P.chart.symm (P.inverseChange 0):=by
      rw [P.inverse_zero]
      exact P.chart.continuousAt_symm h0
    exact hi.comp P.inverse_analytic.continuousAt
  have ht:Tendsto (source P) (𝓝[≠] (0:ℂ)) (𝓝 p):=by
    simpa only [source_zero P] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht hr

theorem regular_dense : Dense RegularSource := by
  intro p
  by_cases hr:p∈RegularSource
  · exact subset_closure hr
  · have hp:=ramified_of_not_regular p hr
    by_cases hi:normalizedMap p=∞
    · exact closure_from_parameter (infinityParameter p hp hi)
        ((infinity_regular (infinityParameter p hp hi)).mono fun _ h=>h.1)
    · let j:=branchIndex p hr hi
      have hj:=branchIndex_value p hr hi
      exact closure_from_parameter (finiteParameter p hp j hj)
        ((finite_regular j (finiteParameter p hp j hj)).mono fun _ h=>h.1)
end PELOriginalContactRegularDensity318
