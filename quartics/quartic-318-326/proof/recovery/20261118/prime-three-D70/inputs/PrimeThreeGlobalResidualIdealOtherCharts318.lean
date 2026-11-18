module
public import PrimeThreeResidualPointChartExclusion318
public import OriginalPrimeThreeSelectedFirstChartAtlas318
public section
noncomputable section
namespace PrimeThreeGlobalResidualIdealOtherCharts318
open AlgebraicGeometry CategoryTheory
open PrimeThreeGlobalResidualIdeal318 PrimeThreeResidualPointChartExclusion318
open OriginalPrimeThreeNativeReesProj318

/-- Because each other first chart is OPEN, exclusion of the actual
point also excludes its closure. No unproved global closed-point assertion
is needed to pass from point exclusion to kernel support exclusion. -/
theorem support_disjoint_other_chart (j : Fin 3) (hj : j ≠ 0) :
    Disjoint (globalResidualIdeal.support : Set actualReesProj)
      (Proj.basicOpen grading (generator j) : Set actualReesProj) := by
  rw [globalResidualIdeal_support]
  refine Disjoint.closure_left ?_ (Proj.basicOpen grading (generator j)).isOpen
  apply Set.disjoint_left.mpr
  rintro y ⟨x, rfl⟩ hy
  exact globalResidualPoint_not_other_chart j hj x hy

/-- Exact unit-ideal restriction on each other native first chart.
This is a statement about native ideal-sheaf data, not only its support. -/
theorem globalResidualIdeal_on_other_native_chart (j : Fin 3) (hj : j ≠ 0) :
    globalResidualIdeal.comap (nativeChartInclusion j) = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change nativeChartInclusion j x ∈ globalResidualIdeal.support ↔ False
  constructor
  · intro hx
    have hr : nativeChartInclusion j x ∈ Proj.basicOpen grading (generator j) := by
      rw [← Proj.opensRange_awayι grading (generator j) (generator_mem j) (by decide)]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp (support_disjoint_other_chart j hj) hx hr
  · exact False.elim

/-- The same literal unit ideal on the already identified retained
arithmetic V/W charts, with their actual inclusion maps. -/
theorem globalResidualIdeal_on_other_arithmetic_chart (j : Fin 3) (hj : j ≠ 0) :
    globalResidualIdeal.comap
      (OriginalPrimeThreeSelectedFirstChartAtlas318.actualChartInclusion j) = ⊤ := by
  change globalResidualIdeal.comap
    ((OriginalPrimeThreeSelectedFirstChartAtlas318.actualChartSpecIso j).inv ≫ nativeChartInclusion j) = _
  rw [Scheme.IdealSheafData.comap_comp, globalResidualIdeal_on_other_native_chart j hj,
    Scheme.IdealSheafData.comap_top]

end PrimeThreeGlobalResidualIdealOtherCharts318
