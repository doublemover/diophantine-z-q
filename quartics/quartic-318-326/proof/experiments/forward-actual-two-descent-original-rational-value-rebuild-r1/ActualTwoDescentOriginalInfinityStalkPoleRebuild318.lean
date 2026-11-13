module
public import ActualTwoDescentOriginalAllPointRootSupportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityStalkPoleRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeFractionFunctions318
variable {K : Type*} [Field K] [CharZero K]

/-- The SAME original generic function, original infinity stalk and actual
local units. This is not an arbitrary field identification. -/
theorem factor (n a : K) :
    ∃ e d : (InfinityStalk n)ˣ,
      infinityV n=(e : InfinityStalk n)*infinityU n^3 ∧
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a *
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n))^2 =
        algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (d : InfinityStalk n) /
          algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (e : InfinityStalk n) := by
  obtain ⟨e,d,he,hd,hv,hr,hunit⟩ :=
    ActualTwoDescentOriginalInfinityNamedPoleRebuild318.normalization n a
  refine ⟨Units.map (infinityEquiv n).symm.toMonoidHom e,
    Units.map (infinityEquiv n).symm.toMonoidHom d, ?_, ?_⟩
  · simpa only [infinityV,infinityU,map_mul,map_pow,Units.coe_map] using
      congrArg (infinityEquiv n).symm he
  · apply (ActualTwoDescentOriginalInfinityLocalFieldRebuild318.comparison n).injective
    simpa only [map_mul,map_pow,map_div₀,
      ActualTwoDescentOriginalInfinityLocalFieldRebuild318.on_stalk,
      infinityU,Units.coe_map,RingEquiv.apply_symm_apply] using hr

theorem fraction (n a : K) :
    ∃ e d : (InfinityStalk n)ˣ,
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a =
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (d : InfinityStalk n) /
          algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (e : InfinityStalk n)) /
        (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n))^2 := by
  obtain ⟨e,d,he,hd⟩ := factor n a
  have hu : algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (ActualTwoDescentOriginalStalkFactorsRebuild318.infinity_uniformizer n).ne_zero
  exact ⟨e,d,(eq_div_iff (pow_ne_zero 2 hu)).mpr hd⟩
end ActualTwoDescentOriginalInfinityStalkPoleRebuild318
