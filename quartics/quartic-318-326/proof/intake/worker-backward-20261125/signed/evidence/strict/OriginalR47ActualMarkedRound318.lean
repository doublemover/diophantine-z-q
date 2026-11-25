module
public import OriginalR47GlobalCentreRees318
public import OriginalR47RetainedPrincipalLift318
import all OriginalR47IsolatedAffineCentres318
public section
noncomputable section

namespace OriginalR47ActualMarkedRound318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47IsolatedCentreCover318 (Centre off)
open OriginalR47GlobalCentreRees318 (source proj marked)
open OriginalR47TraitRoundKernel318 (base)
open OriginalR47RetainedTraitLift318 (eta generic)
open OriginalR47RetainedPrincipalCover318 (eta_point)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
local notation "B" => base (R:=R)
variable {X : Scheme.{u}} [X.IsSeparated]

/-- An end-to-end actual marked repetition step: on the strict global
old Rees scheme itself, the actual centre-free comparison determines
the whole generic lift and the actual properness gives the global
one. No separately supplied proper map, same-coordinate replacement,
or condition that any closed value of P misses a centre. The finite
old centre data are the real inputs of the strict global Rees model. -/
theorem keep (s : X ⟶ B) [LocallyOfFiniteType s]
    (P : B ⟶ X) (hP : P ≫ s = 𝟙 B)
    (Z : Set X) (hZ : Z.Finite) (hC : ∀ z ∈ Z, IsClosed ({z} : Set X))
    (pick : ∀ z : Z, Centre Z z)
    (vert : ∀ z ∈ Z, s z ≠ genericPoint B)
    (fg : ∀ z : Z, (marked pick z).asIdeal.FG) :
    ∃ Qη : Spec (CommRingCat.of (FractionRing R)) ⟶ source Z hZ hC pick,
      Qη ≫ proj Z hZ hC pick = eta (R:=R) ≫ P ∧
      ∃! Q : B ⟶ source Z hZ hC pick,
        eta (R:=R) ≫ Q = Qη ∧ Q ≫ proj Z hZ hC pick = P := by
  let Y := source Z hZ hC pick
  let r := proj Z hZ hC pick
  have hPη : Set.range (eta (R:=R) ≫ P) ⊆ Set.range (off Z hZ hC).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x,rfl⟩
    change (eta (R:=R) ≫ P) x ∉ Z
    intro hx
    have h := congrArg (fun f : B ⟶ B => f (eta (R:=R) x)) hP
    change s (P (eta (R:=R) x)) = eta (R:=R) x at h
    have hs : s ((eta (R:=R) ≫ P) x) = eta (R:=R) x := by
      rw [Scheme.Hom.comp_apply]
      exact h
    exact vert _ hx (hs.trans (eta_point x))
  obtain ⟨a,ha⟩ := OriginalR47GlobalCentreRees318.unchanged Z hZ hC pick
  obtain ⟨Qη,hQη⟩ := generic r (off Z hZ hC).ι P a ha hPη
  let : IsProper r := OriginalR47GlobalCentreRees318.proper Z hZ hC pick fg
  let : Scheme.IsSeparated Y := ⟨by
    rw [← terminal.comp_from r]
    infer_instance⟩
  exact ⟨Qη,hQη,OriginalR47RetainedPrincipalLift318.lift r s P hP Qη hQη⟩

end OriginalR47ActualMarkedRound318

#print axioms OriginalR47ActualMarkedRound318.keep
