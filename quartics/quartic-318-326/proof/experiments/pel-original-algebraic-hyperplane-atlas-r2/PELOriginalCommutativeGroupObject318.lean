module
public import PELOriginalRepresentedAddMonObject318
public import Mathlib.CategoryTheory.Monoidal.Grp
public section
noncomputable section
namespace PELOriginalCommutativeGroupObject318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open PELOriginalProductChartCover318 PELOriginalRepresentedGroupFunctor318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalRepresentedAddMonObject318
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Official Mathlib group object over C, retaining the independently
constructed projective negation and the literal global addition map. -/
instance additiveGroupObject : AddGrpObj (candidateOver τ hτ) where
  neg := Over.homMk (inverse τ hτ) (inverse_over τ hτ)
  left_neg := by
    apply Over.OverMorphism.ext
    change (pullback.lift (inverse τ hτ) (𝟙 _) _)≫
      (AddMonObj.add (X := candidateOver τ hτ)).left=
      π τ hτ≫(AddMonObj.zero (X := candidateOver τ hτ)).left
    rw [addition_underlying,zero_underlying]
    exact left_inverse τ hτ
  right_neg := by
    apply Over.OverMorphism.ext
    change (pullback.lift (𝟙 _) (inverse τ hτ) _)≫
      (AddMonObj.add (X := candidateOver τ hτ)).left=
      π τ hτ≫(AddMonObj.zero (X := candidateOver τ hτ)).left
    rw [addition_underlying,zero_underlying]
    exact right_inverse τ hτ

/-- Commutativity in the actual braided cartesian over-category. -/
instance commutativeObject : IsCommAddMonObj (candidateOver τ hτ) where
  add_comm := by
    apply Over.OverMorphism.ext
    change (pullbackSymmetry (π τ hτ) (π τ hτ)).hom≫
      (AddMonObj.add (X := candidateOver τ hτ)).left=
      (AddMonObj.add (X := candidateOver τ hτ)).left
    rw [addition_underlying]
    have he : (pullbackSymmetry (π τ hτ) (π τ hτ)).hom=
        pullback.lift (pullback.snd (π τ hτ) (π τ hτ))
          (pullback.fst (π τ hτ) (π τ hτ)) pullback.condition.symm := by
      apply pullback.hom_ext <;> simp
    rw [he]
    exact commutative τ hτ

/-- The bundled official group object has the unchanged representing
scheme and original complex structure map. -/
@[expose] def originalGroup : AddGrp (Over (Spec (CommRingCat.of ℂ))) :=
  ⟨candidateOver τ hτ⟩
lemma originalGroup_scheme : (originalGroup τ hτ).X.left=
    PELOriginalReducedProjectiveCandidate318.candidate τ hτ := rfl
lemma originalGroup_base : (originalGroup τ hτ).X.hom=π τ hτ := rfl
lemma originalGroup_inverse : (AddGrpObj.neg (X := (originalGroup τ hτ).X)).left=
    PELOriginalProjectiveNegation318.candidateNegation τ hτ := rfl
end PELOriginalCommutativeGroupObject318
