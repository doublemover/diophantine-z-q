module
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace FiniteComplexPointsScheme318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} (π : X ⟶ Spec (CommRingCat.of ℂ))
abbrev Points := {p : Spec (CommRingCat.of ℂ) ⟶ X // p≫π=𝟙 _}

/-- Finitely many genuine complex-valued points of a locally finite-type
complex scheme force its ENTIRE underlying space to be finite. This uses
Jacobson closed-point density and does not assume reducedness. -/
lemma finite_space [LocallyOfFiniteType π] [Finite (Points π)] : Finite X := by
  let lift : closedPoints X → Points π := fun x =>
    ⟨pointOfClosedPoint π x.val x.property,pointOfClosedPoint_comp π x.val x.property⟩
  have hi : Function.Injective lift := by
    intro x y h
    apply Subtype.ext
    have he := congrArg (fun p : Points π => p.val (IsLocalRing.closedPoint ℂ)) h
    simpa only [lift,pointOfClosedPoint_apply] using he
  letI : Finite (closedPoints X) := Finite.of_injective lift hi
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  have hc : (closedPoints X).Finite := Set.toFinite _
  letI : DiscreteTopology X := JacobsonSpace.discreteTopology hc
  rw [closedPoints_eq_univ] at hc
  exact Set.finite_univ_iff.mp hc

/-- Properness plus the preceding all-prime finiteness gives an actual
finite structural morphism. Multiplicities and nilpotents are retained. -/
lemma finite_morphism [IsProper π] [Finite (Points π)] : IsFinite π := by
  letI : Finite X := finite_space π
  letI : LocallyQuasiFinite π :=
    LocallyQuasiFinite.of_finite_preimage_singleton π (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite π
end FiniteComplexPointsScheme318
