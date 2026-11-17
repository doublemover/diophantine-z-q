module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace IntegralClosureLocalizationField318
variable (A B L : Type*) [CommRing A] [CommRing B] [CommRing L]
  [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]

/-- Inclusion of integral closures under the displayed compatible base
maps. The ambient ring is unchanged. -/
@[expose] def inclusion : integralClosure A L →ₐ[A] integralClosure B L where
  toFun z := ⟨z.val, z.property.tower_top⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[expose] def closureAlgebra : Algebra (integralClosure A L) (integralClosure B L) :=
  (inclusion A B L).toRingHom.toAlgebra
attribute [local instance] closureAlgebra

instance closureBaseTower : IsScalarTower A (integralClosure A L) (integralClosure B L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance closureFieldTower : IsScalarTower (integralClosure A L) (integralClosure B L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The coordinate becomes a unit by its actual image from the localized
base; neither a nonzero-coordinate premise nor a chosen field structure is
needed in this generic version. -/
theorem coordinate_unit (x : A) [IsLocalization.Away x B] :
    IsUnit (algebraMap A L x) := by
  rw [IsScalarTower.algebraMap_apply A B L]
  exact (IsLocalization.Away.algebraMap_isUnit (S := B) x).map (algebraMap B L)

/-- Integral closure commutes with the actual base localization. This also
applies to a reciprocal polynomial action on the same Laurent carrier. -/
theorem localization (x : A) [IsLocalization.Away x B] :
    IsLocalization.Away (algebraMap A (integralClosure A L) x) (integralClosure B L) := by
  letI : IsLocalization.Away (algebraMap A L x) L :=
    IsLocalization.away_of_isUnit_of_bijective L
      (coordinate_unit A B L x) Function.bijective_id
  exact IsLocalization.Away.integralClosure (S := L) (Rf := B) (Sf := L) x

end IntegralClosureLocalizationField318
