module
public import NormalOverlapDifferentialDualTransition318
public import OriginalNormalDualNativeRestrictions318
public section
noncomputable section
namespace OriginalNormalReciprocalDualTransition318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "j" => NormalOverlapReciprocalDualSheaf318.map R a d

/-- Pull back the actual OLD finite trace-sheaf restriction, then apply
the complete reciprocal dual transport and the exact differential unit. -/
@[expose] def finiteRoute :
    (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.restrictFunctor
        (IntegralNormalFiniteDualSheafRestriction318.map R a d)).obj
          (IntegralNormalTraceSheafDuality318.traceSheaf R a d)) ≅
      IntegralNormalInfinityDualSheafRestriction318.overlapDual R a d :=
  (Scheme.Modules.pullback j).mapIso (OriginalNormalDualNativeRestrictions318.finiteIso c t w D) ≪≫
    NormalOverlapDifferentialDualTransition318.sheafIso R a d

/-- A genuine comparison between the two OLD restricted dual sheaves.
Identifying it with the categorical model-chart transition and proving
ambient trace-form compatibility remain separate obligations. -/
@[expose] def chartComparison :
    (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.restrictFunctor
        (IntegralNormalFiniteDualSheafRestriction318.map R a d)).obj
          (IntegralNormalTraceSheafDuality318.traceSheaf R a d)) ≅
      (Scheme.Modules.restrictFunctor
        (IntegralNormalInfinityDualSheafRestriction318.map R a d)).obj
          (OriginalNormalInfinityDuality318.dualSheaf c t w D) :=
  finiteRoute c t w D ≪≫ (OriginalNormalDualNativeRestrictions318.infinityIso c t w D).symm

lemma comparison_infinity :
    (chartComparison c t w D).hom ≫
      (OriginalNormalDualNativeRestrictions318.infinityIso c t w D).hom=
        (finiteRoute c t w D).hom := by
  simp only [chartComparison,Iso.trans_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
end OriginalNormalReciprocalDualTransition318
