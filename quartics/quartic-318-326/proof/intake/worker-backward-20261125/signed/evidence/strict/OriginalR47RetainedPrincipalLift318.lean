module
public import OriginalR47RetainedPrincipalCover318
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public section
noncomputable section

namespace OriginalR47RetainedPrincipalLift318

open AlgebraicGeometry CategoryTheory
open OriginalR47TraitRoundKernel318 (base trait brace)
open OriginalR47RetainedTraitLift318 (eta etaAt etaAt_read)
open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]
local notation "B" => base (R:=R)
local notation "K" => FractionRing R
local notation "G" => Spec (CommRingCat.of K)

section Domain
variable [IsDomain R]

/-- At the zero prime the true original coefficient localization
is the same fraction field. The actual stock algebra map, not a
substitute field isomorphism, induces the inverse generic lift. -/
theorem etaAt_zero : IsIso (etaAt (⊥ : Ideal R)) := by
  let : IsLocalization R⁰ (Localization.AtPrime (⊥ : Ideal R)) :=
    (Ideal.primeCompl_bot (α := R)) ▸ (inferInstance : IsLocalization (⊥ : Ideal R).primeCompl
      (Localization.AtPrime (⊥ : Ideal R)))
  apply isIso_SpecMap_iff.mpr
  exact IsLocalization.bijective R⁰ (algebraMap (Localization.AtPrime (⊥ : Ideal R)) K)
    (IsScalarTower.algebraMap_eq R (Localization.AtPrime (⊥ : Ideal R)) K).symm

end Domain

variable [IsDedekindDomain R]
variable {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
/-- Lift the whole original marked P on the same proper resolved model
using the exact generic choice. The proof needs only the already
pinned ValuativeCriterion and finite-type algebra, not mathematical
rational-map or noetherian spreading stock. -/
theorem lift (r : Y ⟶ X) [IsProper r] (s : X ⟶ B) [LocallyOfFiniteType s]
    (P : B ⟶ X) (hP : P ≫ s = 𝟙 B) (Pη : G ⟶ Y)
    (compatible : Pη ≫ r = eta (R:=R) ≫ P) :
    ∃! Q : B ⟶ Y, eta (R:=R) ≫ Q = Pη ∧ Q ≫ r = P := by
  let t := r ≫ s
  let : LocallyOfFiniteType t := inferInstance
  have hloc (x : PrimeSpectrum R) : ∃ φ : trait x.asIdeal ⟶ Y,
      φ ≫ t = brace x.asIdeal ∧ etaAt x.asIdeal ≫ φ = Pη := by
    by_cases hx : x.asIdeal = ⊥
    · have hx' : x = (⊥ : PrimeSpectrum R) := PrimeSpectrum.ext hx
      subst x
      let : IsIso (etaAt (⊥ : Ideal R)) := etaAt_zero
      let φ : trait (⊥ : Ideal R) ⟶ Y := inv (etaAt (⊥ : Ideal R)) ≫ Pη
      have hφ : etaAt (⊥ : Ideal R) ≫ φ = Pη := by simp only [φ,IsIso.hom_inv_id_assoc]
      refine ⟨φ,?_,hφ⟩
      change φ ≫ t = brace (⊥ : Ideal R)
      apply (cancel_epi (etaAt (⊥ : Ideal R))).mp
      calc
        etaAt (⊥ : Ideal R) ≫ (φ ≫ t) = Pη ≫ (r ≫ s) := by
          rw [← Category.assoc,hφ]
        _ = eta (R:=R) := by rw [← Category.assoc,compatible,Category.assoc,hP,Category.comp_id]
        _ = etaAt (⊥ : Ideal R) ≫ brace (⊥ : Ideal R) := (etaAt_read _).symm
    · obtain ⟨φ,hφ,_⟩ := OriginalR47RetainedTraitLift318.local x.asIdeal r P hx Pη compatible
      refine ⟨φ,?_,hφ.1⟩
      change φ ≫ (r ≫ s) = brace x.asIdeal
      rw [← Category.assoc, hφ.2, Category.assoc, hP, Category.comp_id]
  obtain ⟨Q,hQ,huniq⟩ := OriginalR47RetainedPrincipalCover318.glue t Pη hloc
  let : IsDominant (eta (R:=R)) := OriginalR47RetainedPrincipalCover318.eta_dominates
  have hQr : Q ≫ r = P := by
    apply AlgebraicGeometry.ext_of_isDominant (eta (R:=R))
    rw [← Category.assoc,hQ,compatible]
  exact ⟨Q,⟨hQ,hQr⟩,fun Q' h => huniq Q' h.1⟩

end OriginalR47RetainedPrincipalLift318

#print axioms OriginalR47RetainedPrincipalLift318.etaAt_zero
#print axioms OriginalR47RetainedPrincipalLift318.lift
