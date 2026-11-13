module
public import OriginalNormalOverlapChartEquality318
public import NativeOverlapPullbackComparison318
public section
noncomputable section
namespace OriginalNormalOverlapNativeComparison318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "j" => NormalOverlapReciprocalDualSheaf318.map R a d
local notation "i" => IntegralNormalFiniteDualSheafRestriction318.map R a d
local notation "k" => IntegralNormalInfinityDualSheafRestriction318.map R a d
local instance sourceDomain : IsDomain B :=
  IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)

/-- Every actual whole-model module has this canonical native overlap
comparison on the OLD charts, using the now-proved actual scheme square. -/
@[expose] def globalModule (F : M.scheme.Modules) :
    (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback (OriginalNormalOrderChart318.chart c t w D M)).obj F)) ≅
    (Scheme.Modules.pullback k).obj
      ((Scheme.Modules.pullback (OriginalNormalInfinityChart318.chart c t w D M)).obj F) :=
  NativeOverlapPullbackComparison318.iso j i k
    (OriginalNormalOrderChart318.chart c t w D M)
    (OriginalNormalInfinityChart318.chart c t w D M)
    (OriginalNormalOverlapChartEquality318.square c t w D M) F

/-- The OLD dual comparison, converted through native restriction/pullback
isomorphisms at both ends. This is not yet asserted to arise from globalModule:
that requires full intersection coverage and effective descent. -/
@[expose] def localDual :
    (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback i).obj (IntegralNormalTraceSheafDuality318.traceSheaf R a d)) ≅
    (Scheme.Modules.pullback k).obj (OriginalNormalInfinityDuality318.dualSheaf c t w D) :=
  (Scheme.Modules.pullback j).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback i).app
      (IntegralNormalTraceSheafDuality318.traceSheaf R a d)).symm ≪≫
  OriginalNormalReciprocalDualTransition318.chartComparison c t w D ≪≫
  (Scheme.Modules.restrictFunctorIsoPullback k).app
    (OriginalNormalInfinityDuality318.dualSheaf c t w D)

lemma localDual_normalization :
    (Scheme.Modules.pullback j).map
      ((Scheme.Modules.restrictFunctorIsoPullback i).app
        (IntegralNormalTraceSheafDuality318.traceSheaf R a d)).hom ≫
      (localDual c t w D).hom ≫
      ((Scheme.Modules.restrictFunctorIsoPullback k).app
        (OriginalNormalInfinityDuality318.dualSheaf c t w D)).inv=
    (OriginalNormalReciprocalDualTransition318.chartComparison c t w D).hom := by
  have hc : (Scheme.Modules.pullback j).map
      ((Scheme.Modules.restrictFunctorIsoPullback i).app
        (IntegralNormalTraceSheafDuality318.traceSheaf R a d)).hom ≫
      (Scheme.Modules.pullback j).map
      ((Scheme.Modules.restrictFunctorIsoPullback i).app
        (IntegralNormalTraceSheafDuality318.traceSheaf R a d)).inv=𝟙 _ := by
    rw [←Functor.map_comp,Iso.hom_inv_id,Functor.map_id]
  simp only [localDual,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [←Category.assoc,hc,Category.id_comp]
end OriginalNormalOverlapNativeComparison318
