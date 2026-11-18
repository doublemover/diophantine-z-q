module
public import OriginalIntegerGlobalNormalization318
public import OpenPushoutChartPreimage318
public import OpenPushoutLocalizationRanges318
public section
noncomputable section
namespace OriginalIntegerNormalizationPreimages318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open OriginalIntegerGlobalNormalization318
variable (c : Fin 4 → ℚˣ)
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra

/-- On the finite source chart, crossing to the reciprocal target chart
inverts precisely the image of the original finite parameter. -/
theorem finite_cross :
    finiteProjection c ⁻¹ᵁ (IntegralFourRootGluing318.infinityChart ℤ (d c) a).opensRange =
      (OriginalIntegerNormalizedOverlap318.intoFinite c).opensRange := by
  rw [finiteProjection, Scheme.Hom.comp_preimage,
    OpenPushoutLocalizationRanges318.left_cross]
  letI := OriginalIntegerCommonField318.finiteAlgebra c
  letI := OriginalIntegerCommonField318.finite_localization c
  letI := OriginalIntegerNormalizedOverlap318.overlapAlgebra c
  letI : IsLocalization.Away
      ((OriginalIntegerNormalizationMap318.toClosure c)
        (algebraMap ℤ[X] (OriginalIntegerAffineModel318.Order c) X))
      (OriginalIntegerNormalizedOverlap318.Overlap c) := by
    simpa only [AlgHom.commutes] using OriginalIntegerNormalizedOverlap318.overlap_localization c
  apply TopologicalSpace.Opens.ext
  exact OpenPushoutLocalizationRanges318.away_preimage
    (A' := OriginalIntegerCommonField318.CommonOrder c)
    (B' := OriginalIntegerNormalizedOverlap318.Overlap c)
    (OriginalIntegerNormalizationMap318.toClosure c).toRingHom
    (algebraMap ℤ[X] (OriginalIntegerAffineModel318.Order c) X)

section Reciprocal
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra

/-- On the reciprocal source chart, crossing to the finite target chart
inverts the reciprocal parameter, not a finite-chart scalar or any integer. -/
theorem infinity_cross :
    infinityProjection c ⁻¹ᵁ (IntegralFourRootGluing318.finiteChart ℤ (d c) a).opensRange =
      (OriginalIntegerReciprocalNormalization318.intoInfinity c).opensRange := by
  rw [infinityProjection, Scheme.Hom.comp_preimage,
    OpenPushoutLocalizationRanges318.right_cross]
  letI := OriginalIntegerReciprocalOrderOverlap318.commonAlgebra c
  letI := OriginalIntegerReciprocalOrderOverlap318.localization c
  letI := OriginalIntegerReciprocalNormalization318.overlapAlgebra c
  letI : IsLocalization.Away
      ((OriginalIntegerReciprocalOrderNormalization318.toClosure c)
        (algebraMap ℤ[X] (OriginalIntegerReciprocalCharts318.ReciprocalOrder c) X))
      (OriginalIntegerNormalizedOverlap318.Overlap c) := by
    simpa only [AlgHom.commutes] using OriginalIntegerReciprocalNormalization318.overlap_localization c
  apply TopologicalSpace.Opens.ext
  exact OpenPushoutLocalizationRanges318.away_preimage
    (A' := OriginalIntegerCommonField318.CommonOrder c)
    (B' := OriginalIntegerNormalizedOverlap318.Overlap c)
    (OriginalIntegerReciprocalOrderNormalization318.toClosure c).toRingHom
    (algebraMap ℤ[X] (OriginalIntegerReciprocalCharts318.ReciprocalOrder c) X)
end Reciprocal

/-- The finite normalization chart is the entire finite target-chart preimage. -/
theorem finite_preimage :
    normalization c ⁻¹ᵁ (IntegralFourRootGluing318.finiteChart ℤ (d c) a).opensRange =
      (OriginalIntegerClosureGluing318.finiteChart c).opensRange :=
  OpenPushoutChartPreimage318.preimage
    (OriginalIntegerNormalizedOverlap318.intoFinite c)
    (OriginalIntegerReciprocalNormalization318.intoInfinity c)
    (normalization c) (IntegralFourRootGluing318.finiteChart ℤ (d c) a)
    (finiteMap c) (infinityProjection c)
    (finite_restriction c) (infinity_restriction c) (infinity_cross c)

/-- The reciprocal normalization chart is likewise the entire target preimage. -/
theorem infinity_preimage :
    normalization c ⁻¹ᵁ (IntegralFourRootGluing318.infinityChart ℤ (d c) a).opensRange =
      (OriginalIntegerClosureGluing318.infinityChart c).opensRange := by
  ext x
  change (normalization c x ∈ Set.range (IntegralFourRootGluing318.infinityChart ℤ (d c) a)) ↔
    x ∈ Set.range (OriginalIntegerClosureGluing318.infinityChart c)
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := OpenPushoutChartPreimage318.charts_cover
      (OriginalIntegerNormalizedOverlap318.intoFinite c)
      (OriginalIntegerReciprocalNormalization318.intoInfinity c) x
    · have hp : p ∈ finiteProjection c ⁻¹ᵁ
          (IntegralFourRootGluing318.infinityChart ℤ (d c) a).opensRange := by
        change finiteProjection c p ∈ Set.range _
        have h := congrArg (fun k => k p) (finite_restriction c)
        exact h ▸ hx
      rw [finite_cross] at hp
      obtain ⟨z, hz⟩ := hp
      refine ⟨OriginalIntegerReciprocalNormalization318.intoInfinity c z, ?_⟩
      calc
        OriginalIntegerClosureGluing318.infinityChart c
            (OriginalIntegerReciprocalNormalization318.intoInfinity c z) =
          OriginalIntegerClosureGluing318.finiteChart c
            (OriginalIntegerNormalizedOverlap318.intoFinite c z) :=
          congrArg (fun k => k z) (pushout.condition
            (f := OriginalIntegerNormalizedOverlap318.intoFinite c)
            (g := OriginalIntegerReciprocalNormalization318.intoInfinity c)).symm
        _ = OriginalIntegerClosureGluing318.finiteChart c p :=
          congrArg (OriginalIntegerClosureGluing318.finiteChart c) hz
    · exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    have h := congrArg (fun k => k q) (infinity_restriction c)
    change normalization c (OriginalIntegerClosureGluing318.infinityChart c q) = infinityProjection c q at h
    rw [h]
    exact ⟨infinityMap c q, rfl⟩

theorem finite_pullback : IsPullback (finiteMap c)
    (OriginalIntegerClosureGluing318.finiteChart c)
    (IntegralFourRootGluing318.finiteChart ℤ (d c) a) (normalization c) :=
  IsOpenImmersion.isPullback _ _ _ _ (finite_restriction c) (finite_preimage c)

theorem infinity_pullback : IsPullback (infinityMap c)
    (OriginalIntegerClosureGluing318.infinityChart c)
    (IntegralFourRootGluing318.infinityChart ℤ (d c) a) (normalization c) :=
  IsOpenImmersion.isPullback _ _ _ _ (infinity_restriction c) (infinity_preimage c)

end OriginalIntegerNormalizationPreimages318
