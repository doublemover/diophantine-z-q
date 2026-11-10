module
public import IntegralAllBranchOverlapMaps318
public import LocalizationSourceTransport318
public section
noncomputable section
namespace IntegralFullOverlapLocalization318
open Polynomial
open IntegralSourceBranches318 IntegralBranchDenominatorCover318
open IntegralBranchCoordinates318 IntegralBranchLocalization318
open IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
open IntegralInfinityCommonBase318 IntegralInfinityOverlapRealization318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Squaring the element does not change its actual principal localization.
No reducedness, domain assumption, or radical comparison is used. -/
theorem away_square {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]
    (x : A) [IsLocalization.Away x T] : IsLocalization.Away (x^2) T := by
  simpa only [pow_two] using
    (IsLocalization.Away.mul_of_isUnit (S := T) x x
      (IsLocalization.Away.algebraMap_isUnit (S := T) x))

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
/-- These algebra structures are the existing actual chart restrictions. -/
@[expose] def finiteAlgebra : Algebra (B R c 0) (Overlap R c) :=
  (finiteMap R c).toRingHom.toAlgebra
@[expose] def sourceAlgebra : Algebra (SourceOrder R c) (Overlap R c) :=
  (sourceMap R c).toRingHom.toAlgebra
local instance : Algebra (B R c 0) (Overlap R c) := finiteAlgebra R c
local instance : Algebra (SourceOrder R c) (Overlap R c) := sourceAlgebra R c
local instance sourceSMul : SMul (SourceOrder R c) (Overlap R c) :=
  (sourceAlgebra R c).toSMul
local instance sourceModule : Module (SourceOrder R c) (Overlap R c) := Algebra.toModule
local instance sourceTower : IsScalarTower (SourceOrder R c) (B R c 0) (Overlap R c) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

@[expose] def sourceQuartic : SourceOrder R c :=
  algebraMap R[X] (SourceOrder R c) (IntegralBranchBicanonical318.quartic R)
@[expose] def sourceParameter : SourceOrder R c :=
  algebraMap R[X] (SourceOrder R c) X

/-- The existing tensor overlap is the full localization of the branch-zero
order at its actual root coordinate, along the original finite restriction. -/
theorem root_localization :
    IsLocalization.Away (sourceCoordinate R c 0) (Overlap R c) := by
  letI := rightAlgebra (OpenBase R c 0) (CommonBase R c) (OpenOrder R c 0)
  haveI : IsLocalization.Away
      ((sourceLocalizationEquiv R c 0) (sourceCoordinate R c 0)) (Overlap R c) := by
    simpa only [sourceCoordinate,AlgEquiv.apply_symm_apply,openCoordinate,
      rootCoordinate,LinearRootCoordinate318.inverse_X,rootOpen] using
      (finiteOrder_localization R c)
  exact LocalizationSourceTransport318.away
    (sourceLocalizationEquiv R c 0).toRingEquiv (sourceCoordinate R c 0) (fun _ => rfl)

/-- The original base coordinate t, rather than a new chosen parameter,
defines exactly the same overlap on the branch-zero chart. -/
theorem parameter_localization :
    IsLocalization.Away (sourceT R c 0) (Overlap R c) := by
  letI := root_localization R c
  letI := away_square (T := Overlap R c) (sourceCoordinate R c 0)
  apply IsLocalization.Away.of_associated (r := sourceCoordinate R c 0 ^ 2)
  have he : sourceT R c 0 =
      algebraMap R (B R c 0) (↑(c 0)⁻¹ : R) * sourceCoordinate R c 0 ^ 2 := by
    simpa only [show contacts R 0 = 0 from rfl,map_zero,sub_zero] using
      (coordinate_square R c 0)
  rw [he]
  exact associated_unit_mul_right _ _ (((c 0)⁻¹).isUnit.map (algebraMap R (B R c 0)))

theorem parameter_denominator :
    sourceParameter R c * denominator R c 0 =
      algebraMap R (SourceOrder R c) (twistUnit R c 0 : R) * sourceQuartic R c := by
  have h := congrArg (algebraMap R[X] (SourceOrder R c))
    (IntegralBranchBicanonical318.factor_product_polynomial R c 0)
  have hC (a : R) : algebraMap R[X] (SourceOrder R c) (C a) =
      algebraMap R (SourceOrder R c) a :=
    (IsScalarTower.algebraMap_apply R R[X] (SourceOrder R c) a).symm
  simpa only [show contacts R 0 = 0 from rfl,map_zero,sub_zero,
    map_mul,hC,sourceParameter,denominator,sourceQuartic] using h

/-- The common overlap is the FULL original quartic principal open of the
whole original four-root order. This proves the localization universal
property under the same sourceMap used in the glued model, over every R. -/
theorem whole_localization :
    IsLocalization.Away (sourceQuartic R c) (Overlap R c) := by
  haveI : IsLocalization.Away
      (algebraMap (SourceOrder R c) (B R c 0) (sourceParameter R c)) (Overlap R c) :=
    parameter_localization R c
  haveI : IsLocalization.Away
      (sourceParameter R c * denominator R c 0) (Overlap R c) :=
    IsLocalization.Away.mul (B R c 0) (Overlap R c)
      (denominator R c 0) (sourceParameter R c)
  apply IsLocalization.Away.of_associated
    (r := sourceParameter R c * denominator R c 0)
  rw [parameter_denominator]
  exact (associated_unit_mul_right _ _
    ((twistUnit R c 0).isUnit.map (algebraMap R (SourceOrder R c)))).symm

/-- The universal-property equivalence remembers the original source ring;
it is stronger than an abstract common fraction-field identification. -/
@[expose] def localizationEquiv :
    Localization.Away (sourceQuartic R c) ≃ₐ[SourceOrder R c] Overlap R c := by
  letI := whole_localization R c
  exact IsLocalization.algEquiv (Submonoid.powers (sourceQuartic R c)) _ _

@[simp] theorem localizationEquiv_source (a : SourceOrder R c) :
    localizationEquiv R c (algebraMap (SourceOrder R c)
      (Localization.Away (sourceQuartic R c)) a) = sourceMap R c a :=
  (localizationEquiv R c).commutes a
end IntegralFullOverlapLocalization318
