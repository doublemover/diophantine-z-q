module
public import ContactFieldSectionBaseChange318
public import ProjectiveSectionParameter318
public section
noncomputable section
namespace ContactFieldLinearSectionParameter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve (CommRingCat.of K) c))
local notation "R" => CommRingCat.of K
local instance : Module K Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite K Γ(L.object,⊤) := ContactFieldSectionBaseChange318.finite K c L
local instance : Module.Projective K Γ(L.object,⊤) := inferInstance

/-- A genuine linear section parameter for any original line over a
field, even with nonzero H1. It uses the ACTUAL whole H0, not a guessed rank. -/
abbrev ring := ProjectiveSectionParameter318.algebra K Γ(L.object,⊤)
abbrev scheme : Scheme := Spec (CommRingCat.of (ring K c L))

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra K S := f.toAlgebra
local instance : Module S Γ((L' R S f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) _ ⊤

/-- Both actual point-classification inverses for EVERY field coefficient
algebra, with native geometric meaning supplied by the exact tensor formula. -/
@[expose] def points : (ring K c L →ₐ[K] S) ≃ Γ((L' R S f c L).object,⊤) :=
  (ProjectiveSectionParameter318.points K Γ(L.object,⊤) S).trans
    (ContactFieldSectionBaseChange318.equivalence K c L S f).toEquiv

lemma tensor_value (a : ring K c L →ₐ[K] S) :
    points K c L S f a=ContactFieldSectionBaseChange318.equivalence K c L S f
      (ProjectiveSectionParameter318.points K Γ(L.object,⊤) S a) := rfl
end ContactFieldLinearSectionParameter318
