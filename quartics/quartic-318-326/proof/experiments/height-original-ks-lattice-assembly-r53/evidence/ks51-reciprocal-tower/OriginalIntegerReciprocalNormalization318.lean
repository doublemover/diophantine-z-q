module
public import OriginalIntegerNormalizedOverlap318
public import IntegralClosureLocalizationField318
public import IntegralFourRootOverlap318
public section
noncomputable section
namespace OriginalIntegerReciprocalNormalization318
open Polynomial AlgebraicGeometry CategoryTheory
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Laurent := IntegralWholeReciprocalOverlap318.Laurent ℤ
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Retain the exact finite-chart Laurent action already constructed. -/
@[expose] def laurentAlgebra : Algebra Laurent (L c) :=
  IntegralClosureAwayField318.fieldAlgebra (X : ℤ[X])
    (OriginalIntegerNormalizedOverlap318.parameterUnit c)
attribute [local instance] laurentAlgebra

/-- The reciprocal parameter action is the actual s=1/t map into that
same Laurent ring followed by that same original-field inclusion. -/
@[expose] def reciprocalBaseAlgebra : Algebra ℤ[X] (L c) :=
  ((algebraMap Laurent (L c)).comp
    (IntegralFourRootOverlap318.reciprocalMap ℤ).toRingHom).toAlgebra
attribute [local instance] reciprocalBaseAlgebra

local instance reciprocalLaurentAlgebra : Algebra ℤ[X] Laurent :=
  (IntegralFourRootOverlap318.reciprocalMap ℤ).toRingHom.toAlgebra
local instance reciprocalTower : @IsScalarTower ℤ[X] Laurent (L c)
    reciprocalLaurentAlgebra.toSMul (laurentAlgebra c).toSMul
    (reciprocalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ[X]) (S := Laurent) (A := L c) rfl
local instance reciprocalLocalization : IsLocalization.Away (X : ℤ[X]) Laurent :=
  IntegralWholeReciprocalLocalization318.reciprocal_localization ℤ (fun _ => 1)

/-- Integral closure of the reciprocal parameter ring inside the ORIGINAL
field. Finiteness and comparison with the reciprocal four-root order remain
separate obligations. -/
abbrev Closure := integralClosure ℤ[X] (L c)

/-- The reciprocal normalization and finite normalization have the SAME
localized closure carrier inside L, not merely isomorphic abstract fields. -/
@[expose] def inclusion : Closure c →+* OriginalIntegerNormalizedOverlap318.Overlap c :=
  (IntegralClosureLocalizationField318.inclusion ℤ[X] Laurent (L c)).toRingHom

@[expose] def overlapAlgebra :
    Algebra (Closure c) (OriginalIntegerNormalizedOverlap318.Overlap c) :=
  IntegralClosureLocalizationField318.closureAlgebra ℤ[X] Laurent (L c)
attribute [local instance] overlapAlgebra

theorem overlap_localization :
    IsLocalization.Away (algebraMap ℤ[X] (Closure c) X)
      (OriginalIntegerNormalizedOverlap318.Overlap c) :=
  IntegralClosureLocalizationField318.localization ℤ[X] Laurent (L c) X

theorem inclusion_val (z : Closure c) : (inclusion c z).val = z.val := rfl

theorem inclusion_injective : Function.Injective (inclusion c) := by
  intro z w h
  apply Subtype.ext
  have hv := congrArg
    (fun u : OriginalIntegerNormalizedOverlap318.Overlap c => u.val) h
  simpa only [inclusion_val] using hv

@[expose] def intoInfinity : Spec (CommRingCat.of (OriginalIntegerNormalizedOverlap318.Overlap c)) ⟶
    Spec (CommRingCat.of (Closure c)) :=
  Spec.map (CommRingCat.ofHom (inclusion c))

instance intoInfinity_open : IsOpenImmersion (intoInfinity c) := by
  letI := overlap_localization c
  exact IsOpenImmersion.of_isLocalization (algebraMap ℤ[X] (Closure c) X)

end OriginalIntegerReciprocalNormalization318
