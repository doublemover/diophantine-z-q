module
public import PELOriginalOverlapFunctionEvaluation318
public import FourRootInfinityDomain318
public section
noncomputable section
namespace PELOriginalInfinityFunctionRange318
open PELOriginalCompletedChartEvaluation318 PELOriginalOverlapFunctionEvaluation318
open PELOriginalCommonContactBase318
abbrev InfinityRing := FourRootInfinityCoordinateRing318.Ring branches
abbrev InfinityFunctions := InfinitySource → ℂ

/-- Whole normalized infinity-chart functions on original analytic points,
including all eight u=0 centers and every nonzero overlap point. -/
@[expose] def infinityEvaluation : InfinityRing →ₐ[ℂ] InfinityFunctions where
  toFun a x := infinityAt x a
  map_zero' := funext (fun x => map_zero (infinityAt x))
  map_one' := funext (fun x => map_one (infinityAt x))
  map_add' a b := funext (fun x => map_add (infinityAt x) a b)
  map_mul' a b := funext (fun x => map_mul (infinityAt x) a b)
  commutes' c := funext (fun x => (infinityAt x).commutes c)

lemma toAffineBase_injective : Function.Injective
    (FourRootCoordinateOverlap318.toAffineBase branches) := by
  intro a b h
  apply FourRootInfinityDomain318.localization_injective branches
  apply (FourRootCoordinateOverlap318.overlapEquiv branches).injective
  change FourRootCoordinateOverlap318.toAffine branches
    (algebraMap InfinityRing (FourRootCoordinateOverlap318.InfinityOverlap branches) a) =
    FourRootCoordinateOverlap318.toAffine branches
    (algebraMap InfinityRing (FourRootCoordinateOverlap318.InfinityOverlap branches) b)
  simpa only [FourRootCoordinateOverlap318.toAffine_map] using h

/-- Full original infinity evaluation is faithful: restriction to the actual
regular source is the faithful finite localization composed with the injective
whole-infinity overlap map. No component supported at u=0 is thrown away. -/
theorem infinityEvaluation_injective : Function.Injective infinityEvaluation := by
  intro a b h
  apply toAffineBase_injective
  apply overlapEvaluation_injective
  funext x
  exact (infinity_regular_agreement a x).symm.trans
    ((congrFun h (regularInfinity x)).trans (infinity_regular_agreement b x))

abbrev InfinityAlgebra := infinityEvaluation.range
@[expose] def coefficientMap : InfinityRing →ₐ[ℂ] InfinityAlgebra where
  toFun a := ⟨infinityEvaluation a,⟨a,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero infinityEvaluation)
  map_one' := Subtype.ext (map_one infinityEvaluation)
  map_add' a b := Subtype.ext (map_add infinityEvaluation a b)
  map_mul' a b := Subtype.ext (map_mul infinityEvaluation a b)
  commutes' c := Subtype.ext (infinityEvaluation.commutes c)
lemma coefficientMap_injective : Function.Injective coefficientMap := by
  intro a b h
  exact infinityEvaluation_injective (congrArg Subtype.val h)
lemma coefficientMap_surjective : Function.Surjective coefficientMap := by
  rintro ⟨f,⟨a,ha⟩⟩
  exact ⟨a,Subtype.ext ha⟩
@[expose] def coordinateEquiv : InfinityRing ≃ₐ[ℂ] InfinityAlgebra :=
  AlgEquiv.ofBijective coefficientMap ⟨coefficientMap_injective,coefficientMap_surjective⟩

instance infinityRangeDomain : IsDomain InfinityAlgebra := by
  letI : IsDomain InfinityRing := FourRootInfinityDomain318.infinity_domain branches branches_injective
  exact Function.Injective.isDomain coordinateEquiv.symm coordinateEquiv.symm.injective

lemma original_overlap_value (a : InfinityRing)
    (x : PELOriginalRegularCoordinateAlgebra318.OriginalRegular) :
    (coordinateEquiv a).val (regularInfinity x) =
      overlapEvaluation (FourRootCoordinateOverlap318.toAffineBase branches a) x :=
  infinity_regular_agreement a x

/-- The original labeled action survives on the whole chart, not just its
nonzero principal open or its eight closed center values. -/
lemma infinityEvaluation_deck (w : PELOriginalMaximalQuotient318.Labels)
    (a : InfinityRing) (x : InfinitySource) :
    infinityEvaluation (FourRootCoordinateRingSigns318.infinityEnd branches
      (OriginalContactInertiaBasis318.basis w) a) x =
      infinityEvaluation a (infinityAction w x) :=
  (AlgHom.congr_fun (infinity_deck w x) a).symm
end PELOriginalInfinityFunctionRange318
