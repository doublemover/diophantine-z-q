module
public import OriginalIntegerNormalizationPreimages318
public import OriginalIntegerReciprocalFiniteNormalizationMap318
public import IntegralFourRootProjectiveProper318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace OriginalIntegerGlobalFiniteNormalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalIntegerGlobalNormalization318 OriginalIntegerNormalizationPreimages318
variable (c : Fin 4 → ℚˣ)

instance finiteMap_finite : IsFinite (finiteMap c) := by
  letI := OriginalIntegerNormalizationMap318.closureAlgebra c
  letI := OriginalIntegerNormalizationMap318.finite_normalization c
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap
    (OriginalIntegerAffineModel318.Order c) (OriginalIntegerFiniteClosure318.Closure c))))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance infinityMap_finite : IsFinite (infinityMap c) := by
  letI := OriginalIntegerReciprocalOrderNormalization318.closureAlgebra c
  letI := OriginalIntegerReciprocalFiniteNormalizationMap318.finite c
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap
    (OriginalIntegerReciprocalCharts318.ReciprocalOrder c)
    (OriginalIntegerReciprocalNormalization318.Closure c))))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The actual original two-chart target cover, not a smaller auxiliary cover. -/
abbrev targetCover : (target c).OpenCover where
  I₀ := Bool
  X
    | false => IntegralFourRootGluing318.finiteScheme ℤ (d c) a
    | true => IntegralFourRootGluing318.infinityScheme ℤ (d c) a
  f
    | false => IntegralFourRootGluing318.finiteChart ℤ (d c) a
    | true => IntegralFourRootGluing318.infinityChart ℤ (d c) a
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro p
      obtain ⟨q, hq⟩ | ⟨q, hq⟩ := IntegralFourRootGluing318.charts_cover ℤ (d c) a p
      · exact ⟨false, q, hq⟩
      · exact ⟨true, q, hq⟩
    · intro i
      cases i <;> infer_instance

/-- Finiteness is checked on the WHOLE target-chart pullbacks, identified by
proved preimage equalities. Source-chart finiteness alone is not used as a
substitute for this target-local criterion. -/
instance normalization_finite : IsFinite (normalization c) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) (targetCover c)]
  intro i
  cases i with
  | false =>
    change IsFinite (pullback.snd (normalization c)
      (IntegralFourRootGluing318.finiteChart ℤ (d c) a))
    rw [← (finite_pullback c).flip.isoPullback_inv_snd]
    infer_instance
  | true =>
    change IsFinite (pullback.snd (normalization c)
      (IntegralFourRootGluing318.infinityChart ℤ (d c) a))
    rw [← (infinity_pullback c).flip.isoPullback_inv_snd]
    infer_instance

/-- The normalized integral model maps to Spec Z through the original
whole-order proper model. Rational-fiber comparison and regularity remain
separate, and are not implied by this finite/proper construction. -/
@[expose] def structureMap : source c ⟶ Spec (CommRingCat.of ℤ) :=
  normalization c ≫ IntegralFourRootProjectiveProjection318.structureMap ℤ (d c) a

theorem proper_separated : IsProper (structureMap c) ∧ IsSeparated (structureMap c) := by
  letI := (IntegralFourRootProjectiveProper318.proper_separated ℤ (d c) a).1
  letI := (IntegralFourRootProjectiveProper318.proper_separated ℤ (d c) a).2
  unfold structureMap
  exact ⟨inferInstance, inferInstance⟩

end OriginalIntegerGlobalFiniteNormalization318
