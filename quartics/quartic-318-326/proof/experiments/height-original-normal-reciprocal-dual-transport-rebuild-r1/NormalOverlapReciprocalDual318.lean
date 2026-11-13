module
public import ScalarChangedDualNativeExtension318
public import OriginalNormalOverlapOrderLocalization318
public section
noncomputable section
namespace NormalOverlapReciprocalDual318
open IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open CategoryTheory
universe u
variable (R : Type u) [CommRing R] (a d : Fin 4 → R)
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "A" => FiniteOverlap R a d
local notation "C" => InfinityOverlap R a d
local notation "τ" => LaurentCoordinateInversion318.tau R
local notation "E" => overlapEquiv R a d
local instance : Algebra S A := (IntegralClosureAlongRingMap318.scalar (finiteMap R a d)).toAlgebra
local instance : Algebra S C := (IntegralClosureAlongRingMap318.scalar (infinityMap R a d)).toAlgebra

lemma scalar (s : S) : E (algebraMap S A s)=algebraMap S C (τ s) := by
  apply Subtype.ext
  exact (RingHom.congr_fun (scalar_square R a d) s).symm

/-- Actual finite and reciprocal integral closures inside the SAME open
source. The order map is identity on ambient elements; the base map is tau. -/
@[expose] def equivalence :
    FiniteDualModuleAction318.Dual S A ≃ₛₗ[E.toRingHom]
      FiniteDualModuleAction318.Dual S C :=
  ScalarChangedFiniteDual318.equivalence τ E (scalar R a d)

@[expose] def moduleIso :
    (ModuleCat.extendScalars E.toRingHom).obj
      (ModuleCat.of A (FiniteDualModuleAction318.Dual S A)) ≅
        ModuleCat.of C (FiniteDualModuleAction318.Dual S C) :=
  ScalarChangedDualNativeExtension318.extensionIso τ E (scalar R a d)

lemma value (f : FiniteDualModuleAction318.Dual S A) (x : A) :
    equivalence R a d f (E x)=τ (f x) :=
  ScalarChangedFiniteDual318.at_image τ E (scalar R a d) f x

open scoped TensorProduct in
lemma one_value (f : FiniteDualModuleAction318.Dual S A) (x : A) :
    (moduleIso R a d).hom (1 ⊗ₜ[A,E.toRingHom] f) (E x)=τ (f x) := by
  rw [ScalarChangedDualNativeExtension318.one_value,E.symm_apply_apply]

lemma ambient (x : A) : (E x : OpenOrder R a d)=x.val := rfl
end NormalOverlapReciprocalDual318
