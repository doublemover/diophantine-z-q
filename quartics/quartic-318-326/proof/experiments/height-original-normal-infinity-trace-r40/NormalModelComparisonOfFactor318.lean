module
public import NormalStalkAffineSections318
public section
noncomputable section
namespace NormalModelComparisonOfFactor318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y B : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ B) [QuasiCompact f] [QuasiSeparated f]
  (j : X ⟶ Y) (p : Y ⟶ B) [IsOpenImmersion j] [IsDominant j]
  [IsIntegralHom p] (hf : f=j ≫ p)
  (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

/-- The exact factorization determines a whole-model isomorphism. Its
normalization source is the specified f, not an abstract function field. -/
@[expose] def iso : f.normalization ≅ Y := by
  subst f
  letI : IsIso (DominantFunctionField318.map j) := by
    rw [DominantFunctionField318.map_open]
    infer_instance
  letI := NormalStalkAffineSections318.comparison_isIso j p hn
  exact asIso (NormalizationBirationalComparison318.comparison j p)

@[reassoc] theorem source : f.toNormalization ≫ (iso f j p hf hn).hom=j := by
  subst f
  exact NormalizationBirationalComparison318.comparison_source j p

@[reassoc] theorem base : (iso f j p hf hn).hom ≫ p=f.fromNormalization := by
  subst f
  exact NormalizationBirationalComparison318.comparison_base j p
end NormalModelComparisonOfFactor318
