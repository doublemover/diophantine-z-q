module
public import SplitReducedGauge318
public section
noncomputable section
namespace OriginalOpenExponentialNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpenSections318 OriginalOpenUnitLogarithm318
universe u
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
    {V W : X.Opens} [IsAffine V.toScheme] [IsAffine W.toScheme] (h : W ≤ V)
/-- The exponential uses the ORIGINAL section restriction on both the base
and the entire thickened inverse-image open. -/
lemma exp_restrict (a : Γ(X,V)) :
    Units.map ((thickening R p).presheaf.map (homOfLE ((π R p).preimage_mono h)).op).hom.toMonoidHom
      (exp R p V a) = exp R p W (X.presheaf.map (homOfLE h).op a) := by
  rw [exp_original, exp_original]
  refine (InfinitesimalUnitCocycle318.unit_restrict (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p)
    (DualNumberInfinitesimalLines318.epsilon_square R p)
    ((π R p).preimage_mono h) ((π R p).app V a)).trans ?_
  congr 1
  exact (congrArg (fun f => f a) ((π R p).naturality (homOfLE h).op)).symm
lemma exp_neg (a : Γ(X,V)) : exp R p V (-a) = (exp R p V a)⁻¹ := by
  dsimp only [OriginalOpenUnitLogarithm318.exp]
  rw [map_neg, OriginalAffineUnitLogarithm318.exp_neg, map_inv]
/-- The original zero-section component implies the exact appLE reduction
condition consumed by the complete-open logarithm, retaining its target open. -/
lemma reduced_appLE (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ)
    (hz : Units.map ((reduction R p).app (π R p ⁻¹ᵁ V)).hom.toMonoidHom z = 1) :
    reduce R p V z.val = 1 := by
  have h := congrArg Units.val hz
  change (reduction R p).app (π R p ⁻¹ᵁ V) z.val = 1 at h
  change X.presheaf.map (homOfLE _).op ((reduction R p).app (π R p ⁻¹ᵁ V) z.val) = 1
  rw [h, map_one]
end OriginalOpenExponentialNaturality318
