module
public import NormalizedReciprocalLaurent318
public section
noncomputable section
namespace LaurentCoordinateInversion318
open Polynomial
variable (R : Type*) [CommRing R]
abbrev Base := NormalizedReciprocalLaurent318.Laurent R
abbrev coordinate := NormalizedReciprocalLaurent318.coordinate R

/-- The full Laurent coordinate involution, with no branch factors inverted. -/
@[expose] def tau : Base R ≃+* Base R where
  toFun := NormalizedReciprocalLaurent318.inversion R
  invFun := NormalizedReciprocalLaurent318.inversion R
  left_inv := NormalizedReciprocalLaurent318.inversion_twice R
  right_inv := NormalizedReciprocalLaurent318.inversion_twice R
  map_mul' := (NormalizedReciprocalLaurent318.inversion R).map_mul
  map_add' := (NormalizedReciprocalLaurent318.inversion R).map_add

lemma polynomial (q : R[X]) : tau R (algebraMap R[X] (Base R) q)=
    NormalizedReciprocalLaurent318.reciprocalMap R q :=
  NormalizedReciprocalLaurent318.inversion_polynomial R q
lemma twice (q : Base R) : tau R (tau R q)=q :=
  NormalizedReciprocalLaurent318.inversion_twice R q
lemma coordinate_inverse : tau R (coordinate R : Base R)=(↑(coordinate R)⁻¹ : Base R) :=
  NormalizedReciprocalLaurent318.inversion_coordinate R
end LaurentCoordinateInversion318
