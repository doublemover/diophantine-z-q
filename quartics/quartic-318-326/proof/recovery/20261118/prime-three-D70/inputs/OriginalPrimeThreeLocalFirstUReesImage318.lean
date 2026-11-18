module
public import ReesIdealRatioImage318
public import OriginalPrimeThreeLocalFirstURatioChart318
public section
noncomputable section
namespace OriginalPrimeThreeLocalFirstUReesImage318
open scoped TensorProduct
open PrimeThreeRetainedRootCharts318 PrimeThreeConcreteChartSaturation318
open OriginalPrimeThreeFirstURatioChart318 OriginalPrimeThreeFirstULocalBaseChange318
open OriginalPrimeThreeLocalFirstURatioChart318 OriginalPrimeThreeLocalizedCotangent318
open OriginalPrimeThreeActualRootEquations318
attribute [local instance] OriginalPrimeThreeFirstURatioChart318.chartAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.pointBaseAlgebra

abbrev Center := IsLocalRing.maximalIdeal PointRing
abbrev ActualRees := reesAlgebra Center

/-- Both sides use the same actual maximal ideal, u, coefficient map,
and inverse in PointRing[1/u]. -/
@[expose] def nativeRatioEquiv :
    ReesIdealRatioImage318.ratioAlgebra Center (pointRoot 1) ≃ₐ[PointRing]
      maximalRatioAlgebra := Subalgebra.equivOfEq _ _ rfl

/-- The literal native Rees algebra surjects onto the explicit first-U
chart after actual selected-point base change. Its map is evaluation at
X=1/u, followed by the independently constructed chart equivalence. -/
@[expose] def reesToLocalChart : ActualRees →ₐ[PointRing] LocalChart :=
  actualLocalFirstUIdealRatioEquiv.symm.toAlgHom.comp
    (nativeRatioEquiv.toAlgHom.comp
      (ReesIdealRatioImage318.reesToRatio Center (pointRoot 1)))

theorem reesToLocalChart_surjective : Function.Surjective reesToLocalChart :=
  actualLocalFirstUIdealRatioEquiv.symm.surjective.comp
    (nativeRatioEquiv.surjective.comp
      (ReesIdealRatioImage318.reesToRatio_surjective Center (pointRoot 1)))

theorem reesToLocalChart_eval (f : ActualRees) :
    localChartToPointAway (reesToLocalChart f) =
      ReesIdealRatioImage318.reesEval Center (pointRoot 1) f := by
  rw [← actualLocalFirstUIdealRatioEquiv_coe]
  change (actualLocalFirstUIdealRatioEquiv
      (actualLocalFirstUIdealRatioEquiv.symm
        (nativeRatioEquiv (ReesIdealRatioImage318.reesToRatio Center (pointRoot 1) f))) :
          PointAway) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[expose] def distinguished : ActualRees :=
  ReesIdealRatioImage318.degreeOne Center ⟨pointRoot 1, localRoot_mem_maximal 0⟩

theorem reesToLocalChart_distinguished : reesToLocalChart distinguished = 1 := by
  apply localChartToPointAway_injective
  rw [reesToLocalChart_eval, map_one]
  change ReesIdealRatioImage318.reesEval Center (pointRoot 1)
    (ReesIdealRatioImage318.degreeOne Center ⟨pointRoot 1, localRoot_mem_maximal 0⟩) = 1
  rw [ReesIdealRatioImage318.reesEval_degreeOne]
  exact point_u_mul_inverse

theorem reesToLocalChart_degreeOne_v :
    reesToLocalChart (ReesIdealRatioImage318.degreeOne Center
      ⟨pointRoot 2, localRoot_mem_maximal 1⟩) =
        1 ⊗ₜ[Base] toChart 0 ratioA := by
  apply localChartToPointAway_injective
  rw [reesToLocalChart_eval, ReesIdealRatioImage318.reesEval_degreeOne, localChart_ratioA]
  rfl

theorem reesToLocalChart_degreeOne_w :
    reesToLocalChart (ReesIdealRatioImage318.degreeOne Center
      ⟨pointRoot 3, localRoot_mem_maximal 2⟩) =
        1 ⊗ₜ[Base] toChart 0 ratioB := by
  apply localChartToPointAway_injective
  rw [reesToLocalChart_eval, ReesIdealRatioImage318.reesEval_degreeOne, localChart_ratioB]
  rfl

theorem reesToLocalChart_on_base (a : PointRing) :
    reesToLocalChart (algebraMap PointRing ActualRees a) =
      algebraMap PointRing LocalChart a := reesToLocalChart.commutes a

/-- Only the easy kernel inclusion is asserted here. Equality with this
principal ideal, or identification with degree-zero graded localization,
is still required before claiming a native affine Proj chart. -/
theorem distinguished_relation_le_kernel :
    Ideal.span {distinguished - 1} ≤ RingHom.ker reesToLocalChart.toRingHom := by
  apply Ideal.span_le.mpr
  intro z hz
  have hz' : z = distinguished - 1 := Set.mem_singleton_iff.mp hz
  subst z
  change reesToLocalChart (distinguished - 1) = 0
  rw [map_sub, reesToLocalChart_distinguished, map_one, sub_self]

end OriginalPrimeThreeLocalFirstUReesImage318
