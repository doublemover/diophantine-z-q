module
public import ActualTwoDescentOriginalRootAffineSupport318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootFunctionLocalDivisorData318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootCofactorData318 ActualTwoDescentOriginalRootMaximalIdeal318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentOriginalRootNativeDVR318
open ActualTwoDescentOriginalRootNormalizedOrders318 ActualTwoDescentOriginalRootAffineSupport318
open ActualTwoDescentOriginalFunctionFieldTheta318 ActualTwoDescentLocalizationFractionEquivalence318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDVR318
open ActualTwoDescentInfinityNativeFractionFunctions318 ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentOriginalNativeRootFunctionIdentity318
variable {K : Type*} [Field K] [CharZero K]

/-- Same native original function field, localized at the actual root point. -/
def originalRootLocalFieldEquiv (n : K) (i : Fin 3) :
    OriginalFunctionField n ≃+* FractionRing (RootLocalRing n i) :=
  localizationFractionEquiv (AffineChart n) (RootLocalRing n i) (rootIdeal n i).primeCompl
    (actual_root_local_map_injective n i)
lemma actual_named_root_local_function (n : K) (i : Fin 3) :
    originalRootLocalFieldEquiv n i (rootFunction n (root n i))=
      algebraMap (RootLocalRing n i) (FractionRing (RootLocalRing n i)) (rootLocalF n i) := by
  unfold rootFunction
  rw [actual_root_numerator_class]
  exact actual_localization_fraction_equiv_base (AffineChart n) (RootLocalRing n i)
    (rootIdeal n i).primeCompl (actual_root_local_map_injective n i) (rootNumerator n i)

/-- Produced exact local zero and pole normalizations of the SAME root function.
The zero is order two in the actual root DVR; the pole is order two in
its previously constructed infinity DVR. Naming a global divisor and its
associated section sheaf remains a separate native divisor construction. -/
theorem actual_named_root_zero_and_pole (n : K) (i : Fin 3) [Fact (n≠0)] :
    IsDiscreteValuationRing.addVal (RootLocalRing n i) (rootLocalF n i)=2 ∧
    ∃ z : (RootLocalRing n i)ˣ, ∃ e d : (InfinityLocalRing n)ˣ,
      originalRootLocalFieldEquiv n i (rootFunction n (root n i))=
        algebraMap (RootLocalRing n i) (FractionRing (RootLocalRing n i))
          ((z : RootLocalRing n i)*rootLocalY n i^2) ∧
      originalNativeFunctionFieldEquiv n (rootFunction n (root n i))*
        infinityFractionMap n (localU n)^2=
          infinityFractionMap n (d : InfinityLocalRing n)/infinityFractionMap n (e : InfinityLocalRing n) := by
  obtain ⟨z,hz⟩ := actual_root_local_unit_square n Fact.out i
  obtain ⟨e,d,hv,hd,hpole,hne⟩ := actual_original_root_pole_normalization n (root n i)
  refine ⟨actual_root_order_f n i,z,e,d,?_,hpole⟩
  rw [actual_named_root_local_function,hz]

/-- Exact affine support and local order retain the literal old ideal;
no algebraic-closure or rational-point exhaustion premise is introduced. -/
theorem actual_root_support_and_order (n : K) (i : Fin 3) [Fact (n≠0)] :
    (∀ (P : Ideal (AffineChart n)) [P.IsPrime], rootNumerator n i∈P ↔ P=rootIdeal n i) ∧
    IsDiscreteValuationRing.addVal (RootLocalRing n i) (rootLocalY n i)=1 ∧
    IsDiscreteValuationRing.addVal (RootLocalRing n i) (rootLocalF n i)=2 :=
  ⟨fun P _ => actual_root_prime_support n i P,actual_root_order_y n i,actual_root_order_f n i⟩
end ActualTwoDescentOriginalRootFunctionLocalDivisorData318
