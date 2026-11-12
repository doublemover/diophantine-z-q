module
public import ActualTwoDescentOriginalMarkedStalksRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalStalkFactorsRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentOriginalRootNativeDVR318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDVR318
variable {K : Type*} [Field K] [CharZero K]

theorem root_factor (n : K) (hn : n ≠ 0) (i : Fin 3) :
    ∃ e : (RootStalk n i)ˣ, rootF n i = (e : RootStalk n i) * rootY n i ^ 2 := by
  obtain ⟨e, he⟩ := actual_root_local_unit_square n hn i
  refine ⟨Units.map (rootEquiv n i).symm.toMonoidHom e, ?_⟩
  simpa only [rootF, rootY, map_mul, map_pow, Units.coe_map] using
    congrArg (rootEquiv n i).symm he

theorem infinity_factor (n : K) :
    ∃ e : (InfinityStalk n)ˣ, infinityV n = (e : InfinityStalk n) * infinityU n ^ 3 := by
  obtain ⟨e, he⟩ := actual_local_v_unit_cube n
  refine ⟨Units.map (infinityEquiv n).symm.toMonoidHom e, ?_⟩
  simpa only [infinityV, infinityU, map_mul, map_pow, Units.coe_map] using
    congrArg (infinityEquiv n).symm he

theorem root_uniformizer (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    Irreducible (rootY n i) :=
  (MulEquiv.irreducible_iff (f := (rootEquiv n i).symm.toMulEquiv)).mpr
    (actual_root_y_irreducible n i)

theorem infinity_uniformizer (n : K) : Irreducible (infinityU n) :=
  (MulEquiv.irreducible_iff (f := (infinityEquiv n).symm.toMulEquiv)).mpr
    (actual_infinity_u_irreducible n)
end ActualTwoDescentOriginalStalkFactorsRebuild318
