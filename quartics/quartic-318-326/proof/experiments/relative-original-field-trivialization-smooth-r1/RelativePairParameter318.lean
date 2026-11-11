module
public import ContactCartierDifferenceLine318
public section
noncomputable section
namespace RelativePairParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {S B D : Scheme.{u}} (b : B ⟶ S) (d : D ⟶ S)
abbrev space := pullback b d
abbrev first : space b d ⟶ B := pullback.fst b d
abbrev second : space b d ⟶ D := pullback.snd b d
abbrev projection : space b d ⟶ S := first b d ≫ b
lemma second_over : second b d ≫ d=projection b d := pullback.condition.symm
instance first_flat [Flat d] : Flat (first b d) := inferInstanceAs (Flat (pullback.fst b d))
instance first_surjective [Surjective d] : Surjective (first b d) := inferInstanceAs (Surjective (pullback.fst b d))
instance first_presentation [LocallyOfFinitePresentation d] : LocallyOfFinitePresentation (first b d) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.fst b d))
instance projection_flat [Flat b] [Flat d] : Flat (projection b d) := inferInstanceAs (Flat (first b d ≫ b))
instance projection_surjective [Surjective b] [Surjective d] : Surjective (projection b d) :=
  inferInstanceAs (Surjective (first b d ≫ b))
instance projection_presentation [LocallyOfFinitePresentation b] [LocallyOfFinitePresentation d] :
    LocallyOfFinitePresentation (projection b d) := inferInstanceAs (LocallyOfFinitePresentation (first b d ≫ b))
end RelativePairParameter318
