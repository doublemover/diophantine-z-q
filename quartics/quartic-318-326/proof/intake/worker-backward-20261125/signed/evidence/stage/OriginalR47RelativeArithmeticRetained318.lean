module
public import OriginalR47RelativeArithmeticTermination318
public import OriginalR47RetainedPrincipalLift318
public section
noncomputable section

namespace OriginalR47RelativeArithmeticRetained318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47RelativeArithmeticRound318 (OnTrait ThickOnTrait)
open OriginalR47ActualArithmeticTermination318 (GenericRead)
open OriginalR47RetainedPrincipalCover318 (eta_point)
open OriginalR47RetainedTraitLift318 (eta)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
local notation "S" => Spec (CommRingCat.of R)

variable {X : Scheme} [X.IsSeparated] (s : X ⟶ S) [LocallyOfFiniteType s]
variable (P : S ⟶ X) (hP : P ≫ s = 𝟙 S)

include hP in
/-- On the same actual resolved scheme supplied by the Rees tower,
extend the original marked section, not a new point satisfying only
the same rational coordinate. The final identity is on the original
old scheme, hence retains every original mark read, and includes the
whole generic fibre identity for later comparison with the old π.
Every vertical point of the resulting actual curve has the ordinary
relative chart derived in that same Rees recursion. In particular
this is a statement on this very Q, not a new point with a matching χ. -/
theorem resolve (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (depth : Z → ℕ) (hsite : ∀ z, Nonempty (ThickOnTrait s z.val (depth z)))
    (hreg : ∀ x, x ∉ Z → s x ≠ genericPoint S → OnTrait s x)
    (hvert : ∀ x ∈ Z, s x ≠ genericPoint S) :
    ∃ (Y : Scheme) (r : Y ⟶ X), IsProper r ∧
      (∀ y : Y, (r ≫ s) y ≠ genericPoint S → OnTrait (r ≫ s) y) ∧
      (∀ x : X, _root_.IsConnected (r ⁻¹' ({x} : Set X))) ∧
      GenericRead s r ∧
      ∃! Q : S ⟶ Y, Q ≫ r = P := by
  obtain ⟨Y,r,hpr,hregY,hconn,hGeneric⟩ :=
    OriginalR47RelativeArithmeticTermination318.resolve s Z hZ hC depth hsite hreg hvert
  let : IsProper r := hpr
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from r]; infer_instance⟩
  let g := eta (R:=R) ≫ P
  have h (t : Spec (CommRingCat.of (FractionRing R))) :
      s (g t) = genericPoint S := by
    have hcomp : g ≫ s = eta (R:=R) := by rw [g,Category.assoc,hP,Category.comp_id]
    have H := congrArg (fun k : Spec (CommRingCat.of (FractionRing R)) ⟶ S => k t) hcomp
    rw [Scheme.Hom.comp_apply] at H
    exact H.trans (eta_point t)
  obtain ⟨Qη,H⟩ := hGeneric g h
  have hQη : Qη ≫ r = eta (R:=R) ≫ P := by simpa only [Category.id_comp] using H.w
  obtain ⟨Q,hQ,huniq⟩ := OriginalR47RetainedPrincipalLift318.lift r s P hP Qη hQη
  refine ⟨Y,r,hpr,hregY,hconn,hGeneric,Q,hQ.2,?_⟩
  intro Q' hQ'
  apply huniq Q'
  refine ⟨?_,hQ'⟩
  have hcomm : (eta (R:=R) ≫ Q') ≫ r = (𝟙 _) ≫ g := by
    rw [Category.assoc,hQ',Category.id_comp]
    rfl
  let a := H.lift (eta (R:=R) ≫ Q') (𝟙 _) hcomm
  have ha : a = 𝟙 _ := by
    have hh := H.lift_snd (eta (R:=R) ≫ Q') (𝟙 _) hcomm
    change a ≫ 𝟙 _ = 𝟙 _ at hh
    simpa only [Category.comp_id] using hh
  have hEq := H.lift_fst (eta (R:=R) ≫ Q') (𝟙 _) hcomm
  change a ≫ Qη = eta (R:=R) ≫ Q' at hEq
  rw [ha,Category.id_comp] at hEq
  exact hEq.symm

end OriginalR47RelativeArithmeticRetained318

#print axioms OriginalR47RelativeArithmeticRetained318.resolve
