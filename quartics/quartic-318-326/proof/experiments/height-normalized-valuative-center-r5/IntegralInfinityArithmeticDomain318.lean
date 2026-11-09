module
public import IntegralArithmeticBranchNormal318
public import IntegralOverlapChartMaps318
public section
noncomputable section
namespace IntegralInfinityArithmeticDomain318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralInfinityOverlapRealization318
open scoped TensorProduct nonZeroDivisors
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Abstract native localization injection, before specializing its scalar
structures to the original nested chart rings. -/
theorem away_injective (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] (x : A) [IsLocalization.Away x B] (hx : x≠0) :
    Function.Injective (algebraMap A B) := by
  apply IsLocalization.injective B
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hx)

theorem faithful_injective (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] :
    Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B

variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] (c : Fin 4 → Rˣ)

/-- No coefficient-prime restriction is hidden in the reciprocal denominator:
its constant term is a product of the original twist units. -/
theorem denominator_ne_zero : IntegralInfinityChart318.denominator R c ≠ 0 := by
  intro hz
  have h := (IntegralInfinityChart318.denominator_at_zero_unit R c).ne_zero
  apply h
  rw [hz,Polynomial.eval_zero]

theorem base_domain : IsDomain (IntegralInfinityChart318.Base R c) :=
  Localization.Away.isDomain (denominator_ne_zero R c)

theorem coordinate_base_ne_zero :
    algebraMap R[X] (IntegralInfinityChart318.Base R c) X ≠ 0 := by
  simpa only [map_zero] using
    (away_injective R[X] (IntegralInfinityChart318.Base R c)
      (IntegralInfinityChart318.denominator R c) (denominator_ne_zero R c)).ne
      (Polynomial.X_ne_zero : (X : R[X])≠0)

theorem rootOpen_ne_zero : rootOpen R c ≠ 0 := by
  letI := IntegralArithmeticBranchNormal318.branch_domain R c 0
  have hr : AdjoinRoot.root (QuadraticPresentation318.polynomial
      (LinearRootCoordinate318.parameter (c 0) (contacts R 0))) ≠ 0 := by
    intro hz
    have he := congrArg (LinearRootCoordinate318.forward (c 0) (contacts R 0)) hz
    rw [LinearRootCoordinate318.forward_root,map_zero] at he
    exact Polynomial.X_ne_zero he
  simpa only [rootOpen,map_zero] using
    (away_injective (BranchBase R c 0) (OpenBase R c 0)
      (IntegralBranchChart318.denominator (c 0) (contacts R 0)
        (otherTwist R c 0) (otherContact R 0))
      (IntegralArithmeticBranchNormal318.base_denominator_ne_zero R c 0)).ne hr

/-- The actual common order is a domain because it is the specified principal
localization of the original finite branch domain. -/
theorem finite_overlap_domain (hR : Function.Injective (algebraMap R ℚ)) :
    IsDomain (IntegralOverlapChartMaps318.Overlap R c) := by
  letI := IntegralArithmeticBranchNormal318.open_base_domain R c 0
  letI := IntegralArithmeticBranchNormal318.chart_domain R c hR 0
  letI : Module.FaithfullyFlat (OpenBase R c 0) (OpenOrder R c 0) :=
    ThreeRootOrder318.faithfullyFlat _
  have hn : algebraMap (OpenBase R c 0) (OpenOrder R c 0) (rootOpen R c) ≠ 0 := by
    simpa only [map_zero] using
      (faithful_injective (OpenBase R c 0) (OpenOrder R c 0)).ne (rootOpen_ne_zero R c)
  letI := rightAlgebra (OpenBase R c 0) (CommonBase R c) (OpenOrder R c 0)
  letI := finiteOrder_localization R c
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (IntegralOverlapChartMaps318.Overlap R c)
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hn)

local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

/-- The original infinity order embeds into its actual u-nonzero overlap.
Freeness, rather than an assumed domain structure upstairs, supplies injection. -/
theorem infinity_inclusion_injective : Function.Injective
    (Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
      →ₐ[IntegralInfinityChart318.Base R c]
        CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
          IntegralInfinityChart318.Order R c) := by
  letI := base_domain R c
  letI := IntegralInfinityBaseEquiv318.common_isInfinityLocalization R c
  letI : Module.Free (IntegralInfinityChart318.Base R c)
      (IntegralInfinityChart318.Order R c) := (ThreeRootOrder318.finite_free _).2
  exact Algebra.TensorProduct.includeRight_injective
    (R := IntegralInfinityChart318.Base R c) (A := CommonBase R c)
    (B := IntegralInfinityChart318.Order R c)
    (away_injective (IntegralInfinityChart318.Base R c) (CommonBase R c)
      (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)
      (coordinate_base_ne_zero R c))

/-- Domain structure of the WHOLE original infinity order, including u=0.
Only its injection into the genuine common localization is used, not deletion
of its infinity fiber or selection of a generic component. -/
theorem order_domain (hR : Function.Injective (algebraMap R ℚ)) :
    IsDomain (IntegralInfinityChart318.Order R c) := by
  letI := finite_overlap_domain R c hR
  exact Function.Injective.isDomain (IntegralOverlapChartMaps318.infinityMap R c).toRingHom
    ((actualOverlapEquiv R c).symm.injective.comp (infinity_inclusion_injective R c))
end IntegralInfinityArithmeticDomain318
