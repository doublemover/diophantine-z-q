module
public import PELOriginalTorsionPointComparison318
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public section
noncomputable section
namespace PELOriginalRepresentedAddMonObject318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open PELOriginalProductChartCover318 PELOriginalRepresentedGroupFunctor318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemePointGroup318
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Forget only the already-constructed group inverses; retain the
actual represented additive operations on every complex test scheme. -/
@[expose] def monoidFunctor : (Over (Spec (CommRingCat.of ℂ)))ᵒᵖ ⥤ AddMonCat :=
  groupFunctor τ hτ ⋙ forget₂ AddCommGrpCat AddMonCat

/-- Actual Mathlib representability data on the original object over C.
The natural equivalence retains every morphism, including nilpotent tests. -/
@[expose] def representation :
    (monoidFunctor τ hτ ⋙ forget AddMonCat).RepresentableBy (candidateOver τ hτ) where
  homEquiv {Y} := (pointEquiv τ hτ Y).symm
  homEquiv_comp f g := by apply Subtype.ext; rfl

/-- The official additive monoid object on the SAME candidate in the
cartesian monoidal over-category whose products are actual pullbacks. -/
instance additiveMonoidObject : AddMonObj (candidateOver τ hτ) :=
  AddMonObj.ofRepresentableBy (candidateOver τ hτ) (monoidFunctor τ hτ) (representation τ hτ)

/-- The official zero is the actual original zero section. -/
lemma zero_underlying : (AddMonObj.zero (X := candidateOver τ hτ)).left=zeroPoint τ hτ := by
  change (𝟙 (Spec (CommRingCat.of ℂ)))≫zeroPoint τ hτ=zeroPoint τ hτ
  exact Category.id_comp _

/-- The official multiplication is EXACTLY the already constructed
regular binary scheme morphism, not merely an isomorphic group law. -/
lemma addition_underlying : (AddMonObj.add (X := candidateOver τ hτ)).left=
    PELOriginalAdditionSchemeMorphism318.addition τ hτ := by
  change combine τ hτ (pullback.fst (π τ hτ) (π τ hτ))
    (pullback.snd (π τ hτ) (π τ hτ)) _=_
  have he : pullback.lift (pullback.fst (π τ hτ) (π τ hτ))
      (pullback.snd (π τ hτ) (π τ hτ)) pullback.condition=𝟙 _ := by
    apply pullback.hom_ext <;> simp only [pullback.lift_fst,pullback.lift_snd,Category.id_comp]
  rw [combine,he,Category.id_comp]
end PELOriginalRepresentedAddMonObject318
