module
public import RelativeSectionBaseChange318
public section
noncomputable section
namespace RelativeSectionNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open LineClassPullbackHom318 RelativeLineClassQuotient318
open RelativeLineSectionNormalization318
universe u
variable {X S X' S' : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X)
  (p' : X' ⟶ S') (e' : S' ⟶ X') (a : X' ⟶ X) (b : S' ⟶ S)

lemma restriction_naturality (pointed : e' ≫ a = b ≫ e) (c : Class X) :
    pullback e' (pullback a c) = pullback b (pullback e c) := by
  change LineSheafPullback318.pullback e' (LineSheafPullback318.pullback a c) =
    LineSheafPullback318.pullback b (LineSheafPullback318.pullback e c)
  rw [← LineClassPullbackLaws318.pullback_composition, pointed,
    LineClassPullbackLaws318.pullback_composition]

/-- Original line pullback preserves the original section-restriction kernel
for an actual pointed commuting square. -/
@[expose] def kernelMap (pointed : e' ≫ a = b ≫ e) :
    (pullback e).ker →* (pullback e').ker where
  toFun c := ⟨pullback a c.val, by
    change pullback e' (pullback a c.val) = 1
    rw [restriction_naturality e e' a b pointed, c.property, map_one]⟩
  map_one' := Subtype.ext (map_one (pullback a))
  map_mul' c d := Subtype.ext (map_mul (pullback a) c.val d.val)

/-- Normalization commutes with the actual original pullback, not merely
with a map transported across an abstract group equivalence. -/
lemma normalize_naturality (square : a ≫ p = p' ≫ b)
    (pointed : e' ≫ a = b ≫ e) (c : Class X) :
    pullback a (normalize p e c) = normalize p' e' (pullback a c) := by
  rw [normalize_formula, normalize_formula, map_mul, map_inv]
  have h : pullback a (pullback p (pullback e c)) =
      pullback p' (pullback b (pullback e c)) := by
    change LineSheafPullback318.pullback a
        (LineSheafPullback318.pullback p (pullback e c)) =
      LineSheafPullback318.pullback p'
        (LineSheafPullback318.pullback b (pullback e c))
    rw [← LineClassPullbackLaws318.pullback_composition, square,
      LineClassPullbackLaws318.pullback_composition]
  rw [h, restriction_naturality e e' a b pointed]

/-- The exact quotient/kernel equivalence is natural for original pointed
scheme squares. No degree-zero or represented Picard functor is introduced. -/
lemma equivalence_naturality (section_eq : e ≫ p = 𝟙 S)
    (section_eq' : e' ≫ p' = 𝟙 S') (square : a ≫ p = p' ≫ b)
    (pointed : e' ≫ a = b ≫ e) (c : RelativeClass p) :
    kernelMap e e' a b pointed (equivalence p e section_eq c) =
      equivalence p' e' section_eq' (RelativeLineClassQuotient318.map p p' a b square c) := by
  obtain ⟨d, rfl⟩ := classMap_surjective p c
  apply Subtype.ext
  exact normalize_naturality p e p' e' a b square pointed d
end RelativeSectionNaturality318
