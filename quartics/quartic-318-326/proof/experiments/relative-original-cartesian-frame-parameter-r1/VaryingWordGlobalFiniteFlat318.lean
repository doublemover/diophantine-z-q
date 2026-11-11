module
public import VaryingWordGlobalFamilyCartesian318
public section
noncomputable section
namespace VaryingWordGlobalFiniteFlat318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "p" => VaryingNormalizedUniversalFamily318.projection R A ι
local notation "u" => VaryingWordChartGluing318.into R A ι
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι

private lemma inverse_projection (w : ι → List A) :
    (VaryingWordGlobalFamilyCartesian318.square R A ι w).isoPullback.inv ≫ p w=
      pullback.snd π (u w) :=
  (VaryingWordGlobalFamilyCartesian318.square R A ι w).isoPullback_inv_snd

/-- Finiteness descends from the same actual source-quotient charts through
their genuine Cartesian comparisons over the entire parameter cover. -/
instance finite : IsFinite π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@IsFinite)
    (VaryingWordChartGluing318.cover R A ι)
  intro w
  change IsFinite (pullback.snd π (u w))
  rw [← inverse_projection R A ι w]
  infer_instance
instance flat : Flat π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@Flat)
    (VaryingWordChartGluing318.cover R A ι)
  intro w
  change Flat (pullback.snd π (u w))
  rw [← inverse_projection R A ι w]
  infer_instance

/-- An actual finite-flat global quotient family over the glued word-chart
parameter. This is not yet the global point or Picard classifier. -/
theorem properties : IsFinite π ∧ Flat π := ⟨inferInstance,inferInstance⟩
end VaryingWordGlobalFiniteFlat318
