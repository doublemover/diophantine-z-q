module
public import ActualTwoDescentOriginalRootLocalParameter318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootNativeDVR318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentOriginalRootMaximalIdeal318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentEllipticModel318
variable {K : Type*} [Field K] [CharZero K]

instance rootLocalDomain (n : K) (i : Fin 3) : IsDomain (RootLocalRing n i) :=
  IsLocalization.isDomain_of_local_atPrime (rootIdealPrime n i)
instance affineNoetherian (n : K) : IsNoetherianRing (AffineChart n) :=
  isNoetherianRing_of_surjective (Polynomial (Polynomial K)) (AffineChart n)
    (AdjoinRoot.mk (curve n).toAffine.polynomial) AdjoinRoot.mk_surjective
instance rootLocalNoetherian (n : K) (i : Fin 3) : IsNoetherianRing (RootLocalRing n i) :=
  IsLocalization.isNoetherianRing (rootIdeal n i).primeCompl (RootLocalRing n i) inferInstance

lemma actual_root_maximal_principal (n : K) (hn : n≠0) (i : Fin 3) :
    IsLocalRing.maximalIdeal (RootLocalRing n i)=Ideal.span {rootLocalY n i} := by
  have hm : IsLocalRing.maximalIdeal (RootLocalRing n i)=
      Ideal.span {rootLocalF n i,rootLocalY n i} := by
    rw [←Localization.AtPrime.map_eq_maximalIdeal,actual_root_ideal_generators,
      Ideal.map_span,Set.image_pair]
    rfl
  rw [hm]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl|ha
    · obtain ⟨e,he⟩ := actual_root_local_unit_square n hn i
      rw [he,Ideal.mem_span_singleton]
      refine ⟨(e : RootLocalRing n i)*rootLocalY n i,?_⟩
      ring
    · exact Ideal.subset_span ha
  · exact Ideal.span_mono (by intro a ha; exact Set.mem_insert_of_mem _ ha)

instance rootNativeDVR (n : K) (i : Fin 3) [Fact (n≠0)] :
    IsDiscreteValuationRing (RootLocalRing n i) := by
  have hm : IsLocalRing.maximalIdeal (RootLocalRing n i)≠⊥ := by
    intro h
    have hy := actual_root_local_y_mem n i
    rw [h,Ideal.mem_bot] at hy
    exact actual_root_local_y_nonzero n i hy
  have hn : ¬IsField (RootLocalRing n i) := IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hm
  have hp : (IsLocalRing.maximalIdeal (RootLocalRing n i)).IsPrincipal := by
    rw [actual_root_maximal_principal n Fact.out i]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (RootLocalRing n i) hn).out 5 1).mp hp
lemma actual_root_y_irreducible (n : K) (i : Fin 3) [Fact (n≠0)] :
    Irreducible (rootLocalY n i) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (rootLocalY n i)
    (actual_root_local_y_nonzero n i) (actual_root_maximal_principal n Fact.out i)
end ActualTwoDescentOriginalRootNativeDVR318
