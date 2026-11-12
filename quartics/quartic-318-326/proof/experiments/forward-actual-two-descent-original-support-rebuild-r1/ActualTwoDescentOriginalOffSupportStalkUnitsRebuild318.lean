module
public import ActualTwoDescentOriginalOffOriginAffineCoverRebuild318
public import ActualTwoDescentOriginalRootAffineSupport318
public section
noncomputable section
namespace ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
variable {K : Type*} [Field K] [CharZero K]

lemma named_root (n : K) (i : Fin 3) :
    affineCoefficientMap n (rootNumerator n i)=
      ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i) := by
  rw [ActualTwoDescentOriginalGenericFunctionsRebuild318.root_eq,
    ActualTwoDescentOriginalInfinityGenericIdentityRebuild318.x_affine,
    ActualTwoDescentOriginalInfinityGenericIdentityRebuild318.coefficient_affine]
  exact map_sub (affineCoefficientMap n) _ _

/-- At every off-support scheme point, the SAME named generic root is
the image of an actual unit of its native scheme stalk. -/
theorem unit (n : K) (i : Fin 3) (p : originalCubicScheme n)
    (hroot : p≠rootPoint n i) (hinfty : p≠infinityPoint n) :
    ∃ s : (originalCubicScheme n).presheaf.stalk p,
      IsUnit s ∧ algebraMap ((originalCubicScheme n).presheaf.stalk p)
        (originalCubicScheme n).functionField s=
          ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
            (ActualTwoDescentOriginalRootIdeals318.root n i) := by
  obtain ⟨q,hq⟩ := ActualTwoDescentOriginalOffOriginAffineCoverRebuild318.cover n p hinfty
  subst p
  have hq0 : q.asIdeal≠ActualTwoDescentOriginalRootIdeals318.rootIdeal n i := by
    intro he
    have heq : q=rootPrime n i := PrimeSpectrum.ext he
    apply hroot
    rw [heq] <;> rfl
  let e := ActualTwoDescentOpenAffineStalkRebuild318.equivalence (affineChart n) q
  let s := ActualTwoDescentOpenAffineStalkRebuild318.coefficient
    (affineChart n) q (rootNumerator n i)
  refine ⟨s,?_,?_⟩
  · exact (ActualTwoDescentOriginalRootAffineSupport318.actual_root_unit_off_support
      n i q.asIdeal hq0).map e.symm.toRingHom
  · exact (ActualTwoDescentOpenChartCoefficientRebuild318.stalk_square
      (affineChart n) q (rootNumerator n i)).trans (named_root n i)
end ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318
