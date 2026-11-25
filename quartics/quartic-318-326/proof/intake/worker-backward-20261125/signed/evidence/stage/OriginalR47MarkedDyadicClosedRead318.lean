module
public import OriginalR47ArithmeticFixedPoint318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DedekindDomain.Dvr
public section
noncomputable section

namespace OriginalR47MarkedDyadicClosedRead318

open AlgebraicGeometry CategoryTheory
open OriginalR47TraitRoundKernel318
open OriginalR47InitialArithmeticAtlas318 (fixedPrime)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero R]
local notation "S" => base (R:=R)
variable (p : Ideal R) [p.IsPrime]
local notation "b" => (⟨p,inferInstance⟩ : PrimeSpectrum R)
local notation "c" => IsLocalRing.closedPoint (Localization.AtPrime p)

variable {X : Scheme.{u}} (s : X ⟶ S) [IsSeparated s]
variable (P : S ⟶ X) (hP : P ≫ s = 𝟙 S)

include hP in
/-- The specialization of the actual full section at a genuine dyadic
place is closed on the original scheme. Its canonical trait point
comes from the same section pullback, not from a rational contact or
from any chosen geometric residue fibre of a different cover. -/
theorem old_closed (h₂ : (2 : R) ∈ p) :
    s (P b) = b ∧ IsClosed ({P b} : Set X) ∧
    forgetMap p s (retained p s P hP c) = P b ∧ fixedPrime s (P b) = p := by
  have hp : p ≠ ⊥ := by
    intro hp
    rw [hp, Ideal.mem_bot] at h₂
    exact (Nat.cast_ne_zero.mpr (by decide : (2:ℕ) ≠ 0)) h₂
  have hb : s (P b) = b := by
    have h := congrArg (fun f : S ⟶ S => f b) hP
    change s (P b) = b at h
    exact h
  have hclosed : IsClosed ({b} : Set S) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal b).mpr ((inferInstance : p.IsPrime).isMaximal hp)
  letI : IsClosedImmersion (P ≫ s) := by rw [hP]; infer_instance
  letI : IsClosedImmersion P := IsClosedImmersion.of_comp P s
  have hclosedP : IsClosed ({P b} : Set X) := by
    simpa only [Set.image_singleton] using P.isClosedEmbedding.isClosedMap ({b} : Set S) hclosed
  have hread : forgetMap p s (retained p s P hP c) = P b := by
    have H := congrArg (fun f : trait p ⟶ X => f c) (retained_old p s P hP)
    simpa only [Scheme.Hom.comp_apply,brace_closedPoint] using H
  exact ⟨hb,hclosedP,hread,congrArg PrimeSpectrum.asIdeal hb⟩

variable {Y M : Scheme.{u}} (r : Y ⟶ X) [IsProper r]
variable (Q : S ⟶ Y) (hQr : Q ≫ r = P)
variable (f : X ⟶ M) (retainedR8 : S ⟶ M) (held : P ≫ f = retainedR8)
local notation "s'" => r ≫ s

include hP hQr held in
/-- Applies directly to the Q from the strict actual marked round.
The new closed point lies above exactly the same old closed point,
and its COMPOSED MORPHISM back to R8 is the previously held section.
The universal old trait point and both indicated closed-point maps
are those of the same Cartesian round. -/
theorem on_same_round (h₂ : (2 : R) ∈ p) :
    Q ≫ r ≫ f = retainedR8 ∧
      IsClosed ({Q b} : Set Y) ∧ r (Q b) = P b ∧
      a p s r (retainedRound p s r Q (by rw [← Category.assoc,hQr,hP]) c) =
        retained p s P hP c := by
  have hQ : Q ≫ s' = 𝟙 S := by rw [← Category.assoc,hQr,hP]
  have eq : r (Q b) = P b := by
    have H := congrArg (fun j : S ⟶ X => j b) hQr
    exact H
  have close := (old_closed p s' Q hQ h₂).2.1
  refine ⟨by rw [← Category.assoc,hQr,held],close,eq,?_⟩
  have H := congrArg (fun j : trait p ⟶ restricted p s => j c)
    (retainedRound_down p s r Q hQ)
  rw [Scheme.Hom.comp_apply] at H
  have retEq (P' : S ⟶ X) (hP' : P' ≫ s = 𝟙 S) (e : P' = P) :
      retained p s P' hP' = retained p s P hP := by
    subst P'
    rfl
  exact H.trans (congrArg (fun j : trait p ⟶ restricted p s => j c) (retEq _ _ hQr))

end OriginalR47MarkedDyadicClosedRead318

#print axioms OriginalR47MarkedDyadicClosedRead318.old_closed
#print axioms OriginalR47MarkedDyadicClosedRead318.on_same_round
