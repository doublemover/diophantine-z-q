module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace IntegralClosureAwayField318
variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]
variable (x : A) (hx : IsUnit (algebraMap A L x))

/-- Extend the given coefficient map, rather than choose an unrelated
algebra structure on the ambient field. -/
@[expose] def fieldMap : Localization.Away x →+* L :=
  IsLocalization.Away.lift x hx

@[expose] def fieldAlgebra : Algebra (Localization.Away x) L :=
  (fieldMap x hx).toAlgebra

@[simp] theorem fieldMap_on_base (a : A) :
    fieldMap x hx (algebraMap A (Localization.Away x) a) = algebraMap A L a :=
  IsLocalization.Away.lift_eq x hx a

-- The unit proof is supplied explicitly, not inferred from an Algebra goal.
instance fieldTower :
    letI := fieldAlgebra x hx
    IsScalarTower A (Localization.Away x) L := by
  letI := fieldAlgebra x hx
  exact IsScalarTower.of_algebraMap_eq (R := A) (S := Localization.Away x) (A := L)
    (fun a => (fieldMap_on_base x hx a).symm)

abbrev Closure := integralClosure A L
abbrev AwayClosure :=
  letI := fieldAlgebra x hx
  integralClosure (Localization.Away x) L

/-- The actual inclusion between closures inside the SAME ambient field.
The integrality proof uses the explicitly extended coefficient action. -/
@[expose] def inclusion :
    letI := fieldAlgebra x hx
    Closure (A := A) (L := L) →ₐ[A] AwayClosure x hx := by
  letI := fieldAlgebra x hx
  exact
    { toFun := fun z => ⟨z.val, z.property.tower_top⟩
      map_one' := Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      commutes' := fun _ => Subtype.ext rfl }

@[simp] theorem inclusion_val (z : Closure (A := A) (L := L)) :
    (inclusion x hx z).val = z.val := rfl

theorem inclusion_injective : Function.Injective (inclusion x hx) := by
  intro z w h
  exact Subtype.ext (congrArg Subtype.val h)

@[expose] def closureAlgebra :
    Algebra (Closure (A := A) (L := L)) (AwayClosure x hx) :=
  (inclusion x hx).toRingHom.toAlgebra
attribute [local instance] closureAlgebra

instance closureBaseTower :
    letI := fieldAlgebra x hx
    IsScalarTower A (Closure (A := A) (L := L)) (AwayClosure x hx) := by
  letI := fieldAlgebra x hx
  exact IsScalarTower.of_algebraMap_eq
    (fun a => ((inclusion x hx).commutes a).symm)

instance closureFieldTower :
    letI := fieldAlgebra x hx
    IsScalarTower (Closure (A := A) (L := L)) (AwayClosure x hx) L := by
  letI := fieldAlgebra x hx
  exact IsScalarTower.of_algebraMap_eq'
    (R := Closure (A := A) (L := L)) (S := AwayClosure x hx) (A := L) rfl

/-- Normalization commutes with this coordinate localization. All scalar
maps and compatibility instances above are constructed, not hypotheses.
Only the coordinate x is inverted; this does not invert residue primes. -/
theorem localization :
    IsLocalization.Away (algebraMap A (Closure (A := A) (L := L)) x)
      (AwayClosure x hx) := by
  letI := fieldAlgebra x hx
  letI : IsLocalization.Away (algebraMap A L x) L :=
    IsLocalization.away_of_isUnit_of_bijective L hx Function.bijective_id
  exact IsLocalization.Away.integralClosure (S := L)
    (Rf := Localization.Away x) (Sf := L) x

end IntegralClosureAwayField318
