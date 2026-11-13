module
public import IntegralOriginalNormalOverlap318
public import IntegralClosurePrincipalLocalization318
public import OriginalNormalInfinityTraceLattice318
public section
noncomputable section
namespace OriginalNormalOverlapOrderLocalization318
open Polynomial IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "B" => OpenOrder R a d
local notation "Nf" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "Of" => FiniteOverlap R a d
local notation "Oi" => InfinityOverlap R a d

@[instance_reducible] def finiteAlgebra : Algebra S B := (finiteMap R a d).toAlgebra
@[instance_reducible] def infinityAlgebra : Algebra S B := (infinityMap R a d).toAlgebra

section Finite
local instance : Algebra S B := finiteAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (finite_polynomial R a d q).symm)

@[expose] def finiteInclusion : Nf →+* Of :=
  (IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=S) (B:=B)).toRingHom
@[instance_reducible] def finiteNormalAlgebra : Algebra Nf Of :=
  (finiteInclusion R a d).toAlgebra

lemma finite_inclusion_value (z : Nf) : (finiteInclusion R a d z:B)=z.val := rfl

/-- All normal elements on the punctured finite chart arise by inverting
only the original t coordinate in the whole finite normal order. -/
lemma finite_localization :
    letI := finiteNormalAlgebra R a d
    IsLocalization.Away (algebraMap P Nf X) Of := by
  letI := finiteNormalAlgebra R a d
  exact IntegralClosurePrincipalLocalization318.localization (Q:=S) (B:=B) (X:P)
end Finite

section Infinity
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : Algebra S B := infinityAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (RingHom.congr_fun (infinity_polynomial R a d) q).symm)
local notation "Ni" => IntegralInfinityNormalConductor318.normalOrder R a d

@[expose] def infinityInclusion : Ni →+* Oi :=
  (IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=S) (B:=B)).toRingHom
@[instance_reducible] def infinityNormalAlgebra : Algebra Ni Oi :=
  (infinityInclusion R a d).toAlgebra
lemma infinity_inclusion_value (z : Ni) : (infinityInclusion R a d z:B)=z.val := rfl

/-- The reciprocal result uses the OLD reciprocal polynomial action on
B, not the finite action with a renamed coordinate. -/
lemma infinity_localization :
    letI := infinityNormalAlgebra R a d
    IsLocalization.Away (algebraMap P Ni X) Oi := by
  letI := infinityNormalAlgebra R a d
  exact IntegralClosurePrincipalLocalization318.localization (Q:=S) (B:=B) (X:P)
end Infinity
end OriginalNormalOverlapOrderLocalization318

namespace OriginalNormalOverlapSignedPoint318
open NumberField OriginalPointFinitePlaceRoots318
open OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients

/-- Same literal ambient element, hence the SAME signed point evaluation.
This does not identify either trace lattice or its differential frame. -/
lemma overlap_value (z : IntegralOriginalNormalOverlap318.FiniteOverlap R a d) :
    M.fieldPoint (IntegralOriginalNormalOverlap318.overlapEquiv R a d z).val=
      M.fieldPoint z.val := rfl
end OriginalNormalOverlapSignedPoint318
