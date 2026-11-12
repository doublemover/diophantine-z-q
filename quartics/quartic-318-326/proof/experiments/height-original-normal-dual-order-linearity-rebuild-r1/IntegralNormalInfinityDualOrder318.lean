module
public import IntegralClosureDualOrderBaseChange318
public section
noncomputable section
namespace IntegralNormalInfinityDualOrder318
open Polynomial IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open scoped TensorProduct
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "B" => OpenOrder R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : Algebra S B := OriginalNormalOverlapOrderLocalization318.infinityAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (RingHom.congr_fun (infinity_polynomial R a d) q).symm)
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "O" => InfinityOverlap R a d
local instance : Algebra N O := IntegralClosureLocalizationMap318.normalAlgebra
local instance : Module N (N →ₗ[P] P) := ValuedDualPrecomposition318.actionModule P N P
local instance : Module O (O →ₗ[P] S) := ValuedDualPrecomposition318.actionModule P O S

/-- Whole normal-order linear localization on the literal infinity chart.
No identification of independent finite and reciprocal scalar actions. -/
@[expose] def equivalence : O ⊗[N] (N →ₗ[P] P) ≃ₗ[O] (O →ₗ[P] S) := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureDualOrderBaseChange318.equivalence (Q:=S) (B:=B) (X:P)

lemma one_value (f : N →ₗ[P] P) (n : N) :
    equivalence R a d hd (1 ⊗ₜ[N] f)
      (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d n)=algebraMap P S (f n) := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureDualOrderBaseChange318.one_value (Q:=S) (B:=B) (X:P) f n

lemma integral_tensor_value (x n : N) (f : N →ₗ[P] P) :
    equivalence R a d hd
      (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d x ⊗ₜ[N] f)
      (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d n)=
      algebraMap P S (f (x*n)) := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureDualOrderBaseChange318.integral_tensor_value (Q:=S) (B:=B) (X:P) x n f
end IntegralNormalInfinityDualOrder318
