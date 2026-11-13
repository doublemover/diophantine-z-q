module
public import NormalOverlapFinitePresentation318
public import IntegralClosureFullDualLocalization318
public import OriginalNormalOverlapOrderLocalization318
public import IntegralInfinityTraceFunctional318
public section
noncomputable section
namespace IntegralNormalOverlapInfinityDual318
open Polynomial IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open scoped TensorProduct
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "O" => InfinityOverlap R a d
local notation "L" => IntegralInfinityNormalConductor318.codifferent R a d
local instance : Algebra S B := OriginalNormalOverlapOrderLocalization318.infinityAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (RingHom.congr_fun (infinity_polynomial R a d) q).symm)

@[expose] def map : (N →ₗ[P] P) →ₗ[P] (O →ₗ[P] S) :=
  IntegralClosureFullDualLocalization318.map (Q:=S) (B:=B) (X:P)

@[expose] def equivalence : S ⊗[P] (N →ₗ[P] P) ≃ₗ[S] (O →ₗ[P] S) := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureFullDualLocalization318.equivalence (Q:=S) (B:=B) (X:P)

lemma map_value (f : N →ₗ[P] P) (n : N) :
    map R a d f (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d n)=
      algebraMap P S (f n) :=
  IntegralClosureFullDualLocalization318.map_value (Q:=S) (B:=B) (X:P) f n

lemma one_value (f : N →ₗ[P] P) (n : N) :
    equivalence R a d hd (1 ⊗ₜ[P] f)
      (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d n)=
      algebraMap P S (f n) := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureFullDualLocalization318.one_value (Q:=S) (B:=B) (X:P) f n

/-- Retain the actual old trace coefficient and both scalar destinations.
No equality of the two overlap trace lattices is inferred. -/
theorem trace_coefficient (z : L) (n : N) :
    ∃ p : P,
      map R a d (IntegralInfinityTraceFunctional318.equivalence R a d hd z)
        (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d n)=algebraMap P S p ∧
      algebraMap P F p=Algebra.trace F B (z.val*n.val) :=
  ⟨_,map_value R a d _ n,IntegralInfinityTraceFunctional318.trace_value R a d hd z n⟩
end IntegralNormalOverlapInfinityDual318
