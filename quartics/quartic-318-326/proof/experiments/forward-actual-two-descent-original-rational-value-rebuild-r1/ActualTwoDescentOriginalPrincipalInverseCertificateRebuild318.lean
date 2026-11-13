module
public import ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Exact opposite sign for the inverse function. This distinguishes
O(O-Ta) and O(Ta-O) before any associated-sheaf comparison. -/
theorem root_order (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = (-2 : WithTop ℤ) := by
  rw [(ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i).map_inv,
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.named_root]
  norm_num

theorem infinity_order (n a : K) :
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a)⁻¹ = (2 : WithTop ℤ) := by
  rw [(ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n).map_inv,
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.named_root]
  norm_num

/-- A combined actual inverse certificate, with all off-support points
and actual stalk embeddings rather than selected geometric points. -/
theorem all_points (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = -2 ∧
    ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ = 2 ∧
    ∀ p : originalCubicScheme n, p ≠ rootPoint n i → p ≠ infinityPoint n →
      ∃ s : ((originalCubicScheme n).presheaf.stalk p)ˣ,
        algebraMap ((originalCubicScheme n).presheaf.stalk p) (originalCubicScheme n).functionField
          (s : (originalCubicScheme n).presheaf.stalk p) =
        (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
          (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ :=
  ⟨root_order n i,infinity_order n _,
    ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318.inverse_unit n i⟩
end ActualTwoDescentOriginalPrincipalInverseCertificateRebuild318
