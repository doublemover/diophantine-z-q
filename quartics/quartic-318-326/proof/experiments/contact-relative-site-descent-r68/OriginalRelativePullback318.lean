module
public import ContactRelativeOpenSieve318
public section
noncomputable section
namespace OriginalRelativePullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalRelativeSite318
universe u
variable {X Y Z B : Scheme.{u}} (b : Y ⟶ B) (b' : X ⟶ B) (c : Z ⟶ B)
  (f : X ⟶ Y) (hf : f ≫ b = b') (g : Z ⟶ Y) (hg : g ≫ b = c)
abbrev base : pullback f g ⟶ B := pullback.snd f g ≫ c
include hf hg in
lemma first_base : pullback.fst f g ≫ b' = base c f g := by
  rw [← hf,← Category.assoc,pullback.condition,Category.assoc,hg]
abbrev first : object (base c f g) ⟶ object b' :=
  arrow b' (base c f g) (pullback.fst f g) (first_base b b' c f hf g hg)
abbrev second : object (base c f g) ⟶ object c :=
  arrow c (base c f g) (pullback.snd f g) rfl
lemma square : second c f g ≫ arrow b c g hg = first b b' c f hf g hg ≫ arrow b b' f hf := by
  ext
  exact pullback.condition.symm
end OriginalRelativePullback318
