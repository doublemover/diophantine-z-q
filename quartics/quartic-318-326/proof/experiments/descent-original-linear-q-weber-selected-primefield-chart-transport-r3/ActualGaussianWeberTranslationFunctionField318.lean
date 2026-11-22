module
public import ActualGaussianWeberTranslationChart318
public section
noncomputable section

namespace ActualGaussianWeberTranslationFunctionField318

open Polynomial
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationChart318

variable (K : Type*) [Field K]

@[expose] def fractionMap : Chart K→+*FunctionField K :=
  algebraMap (Chart K) (FunctionField K)

theorem fractionMap_injective : Function.Injective (fractionMap K) :=
  IsFractionRing.injective (Chart K) (FunctionField K)

@[expose] def xGeneric : FunctionField K := fractionMap K (xChart K)
@[expose] def yGeneric : FunctionField K := fractionMap K (yChart K)
@[expose] def constGeneric : K→+*FunctionField K :=
  (fractionMap K).comp ((AdjoinRoot.of (relation K)).comp C)

theorem xGeneric_ne : xGeneric K≠0 := by
  intro h
  apply xChart_ne K
  exact fractionMap_injective K (h.trans (map_zero (fractionMap K)).symm)

theorem equation_generic : (yGeneric K)^2=(xGeneric K)^3-xGeneric K := by
  have h := congrArg (fractionMap K) (equation_chart K)
  simpa only [map_pow,map_sub,xGeneric,yGeneric] using h

theorem generic_unit : IsUnit (fractionMap K (xChart K)) :=
  isUnit_iff_ne_zero.mpr (xGeneric_ne K)

@[expose] def openToFraction : XOpen K→+*FunctionField K :=
  IsLocalization.Away.lift (S:=XOpen K) (xChart K) (generic_unit K)

theorem openToFraction_chart (a : Chart K) :
    openToFraction K (chartMap K a)=fractionMap K a :=
  IsLocalization.Away.lift_eq _ _ _

theorem chartMap_injective : Function.Injective (chartMap K) := by
  intro a b h
  apply fractionMap_injective K
  simpa only [openToFraction_chart] using congrArg (openToFraction K) h

theorem openToFraction_injective : Function.Injective (openToFraction K) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (xChart K)) (openToFraction K)).mpr
  intro a b
  change chartMap K a=chartMap K b ↔ openToFraction K (chartMap K a)=openToFraction K (chartMap K b)
  simp only [openToFraction_chart]
  exact ⟨fun h => congrArg (fractionMap K) (chartMap_injective K h),
    fun h => congrArg (chartMap K) (fractionMap_injective K h)⟩

theorem openToFraction_x : openToFraction K (z K)=xGeneric K :=
  openToFraction_chart K (xChart K)

theorem openToFraction_y : openToFraction K (w K)=yGeneric K :=
  openToFraction_chart K (yChart K)

theorem openToFraction_inv : openToFraction K (zi K)=(xGeneric K)⁻¹ := by
  have h := congrArg (openToFraction K) (zzi K)
  simp only [map_mul,map_one,openToFraction_x] at h
  apply mul_left_cancel₀ (xGeneric_ne K)
  exact h.trans (mul_inv_cancel₀ (xGeneric_ne K)).symm

@[expose] def chartTranslate : Chart K→+*FunctionField K :=
  (openToFraction K).comp ((translateOpen K).comp (chartMap K))

theorem chartTranslate_injective : Function.Injective (chartTranslate K) :=
  (openToFraction_injective K).comp ((translateOpen_injective K).comp (chartMap_injective K))

/-- Actual field homomorphism induced by translation by the
nonzero rational 2-torsion. Its construction needs no geometric
automorphism theorem or pointwise rational-function oracle. -/
@[expose] def translateFrac : FunctionField K→+*FunctionField K :=
  IsFractionRing.lift (chartTranslate_injective K)

theorem translate_fraction_chart (a : Chart K) :
    translateFrac K (fractionMap K a)=openToFraction K (translateOpen K (chartMap K a)) :=
  IsFractionRing.lift_algebraMap (chartTranslate_injective K) a

theorem translate_fraction_x : translateFrac K (xGeneric K)= -1/xGeneric K := by
  change translateFrac K (fractionMap K (xChart K))=_
  rw [translate_fraction_chart]
  change openToFraction K (translateOpen K (z K))=_
  rw [translate_open_x,map_neg,openToFraction_inv,neg_div,one_div]

theorem translate_fraction_y : translateFrac K (yGeneric K)=yGeneric K/(xGeneric K)^2 := by
  change translateFrac K (fractionMap K (yChart K))=_
  rw [translate_fraction_chart]
  change openToFraction K (translateOpen K (w K))=_
  rw [translate_open_y,map_mul,map_pow,openToFraction_y,openToFraction_inv,
      div_eq_mul_inv,inv_pow]

theorem translate_fraction_const (c : K) :
    translateFrac K (constGeneric K c)=constGeneric K c := by
  change translateFrac K (fractionMap K (AdjoinRoot.of (relation K) (C c)))=_
  rw [translate_fraction_chart]
  change openToFraction K (translateOpen K (constants K c))=
    fractionMap K (AdjoinRoot.of (relation K) (C c))
  rw [translate_open_const]
  exact openToFraction_chart K _

end ActualGaussianWeberTranslationFunctionField318
