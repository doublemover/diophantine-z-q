module
public import TensorComplexPointSeparation318
public import PELOriginalChartPointSeparation318
public section
noncomputable section
namespace PELOriginalProductChartPoints318
open scoped TensorProduct
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)
abbrev ProductRing := CoordinateChart τ hτ j ⊗[ℂ] CoordinateChart τ hτ k

/-- Every tensor element, including mixed sums, is separated by pairs
of actual complex points of the two full original coordinate charts. -/
theorem ext (a b : ProductRing τ hτ j k)
    (h : ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      ∀ g : CoordinateChart τ hτ k →ₐ[ℂ] ℂ,
      TensorComplexPointSeparation318.evaluation f g a=
        TensorComplexPointSeparation318.evaluation f g b) : a=b := by
  apply TensorComplexPointSeparation318.ext ?_ ?_ a b h
  · intro x hx
    apply PELOriginalChartPointSeparation318.ext τ hτ j
    intro f
    rw [hx f,map_zero]
  · intro x hx
    apply PELOriginalChartPointSeparation318.ext τ hτ k
    intro g
    rw [hx g,map_zero]

/-- Reducedness of the ACTUAL product coordinate ring is produced,
not assumed from pointwise equations. It justifies later whole-scheme
factorization of the addition tensor through reduced target relations. -/
instance productReduced : IsReduced (ProductRing τ hτ j k) where
  eq_zero a ha := by
    apply ext τ hτ j k
    intro f g
    rw [map_zero]
    exact isNilpotent_iff_eq_zero.mp (ha.map (TensorComplexPointSeparation318.evaluation f g))
end PELOriginalProductChartPoints318
