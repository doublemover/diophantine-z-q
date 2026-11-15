module
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public section
noncomputable section
namespace SeparatedValuationCenterEquality318
open AlgebraicGeometry CategoryTheory
universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X Y : Scheme.{u}} (p : X ⟶ Y) [IsSeparated p]

/-- Two actual valuation-ring centers of the SAME field point and
base section are equal by the native uniqueness half of the criterion. -/
theorem eq (g h : Spec (CommRingCat.of R) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g=
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ h)
    (hb : g ≫ p=h ≫ p) : g=h := by
  let S : ValuativeCommSq p :=
    { R := R, K := K
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g
      i₂ := g ≫ p
      commSq := ⟨Category.assoc _ _ _⟩ }
  letI : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion p S
  let G : S.commSq.LiftStruct := ⟨g,rfl,rfl⟩
  let H : S.commSq.LiftStruct := ⟨h,hg.symm,hb.symm⟩
  exact congrArg CategoryTheory.CommSq.LiftStruct.l (Subsingleton.elim G H)
end SeparatedValuationCenterEquality318
