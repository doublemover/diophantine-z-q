module
public import IntegralNormalSourcePoint318
public import IntegralTwoChartNormalization318
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public section
noncomputable section
namespace IntegralNormalPointCenter318
open Polynomial CategoryTheory AlgebraicGeometry
open IntegralDistinctContactOpen318 IntegralNormalSourcePoint318
set_option maxHeartbeats 1200000
universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] [ValuationRing R]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  (a d : Fin 4 → R) [IsDomain (OpenOrder R a d)]
  [Module.Finite (Base R a d) (OpenOrder R a d)]
  [Algebra.Etale (Base R a d) (OpenOrder R a d)]
  (t : K) (hd : ∀ i, algebraMap R K (d i) ≠ 0)
  (ht : t ≠ 0) (hn : ∀ i, t-algebraMap R K (a i) ≠ 0)
  (z : Fin 4 → K) (hz : ∀ i, (z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i)))

abbrev model := IntegralTwoChartNormalization318.model R a (arithmeticDenominator R d)
  (OpenOrder R a d)
abbrev structureMap := IntegralTwoChartNormalization318.structureMap R a (arithmeticDenominator R d)
  (OpenOrder R a d)
abbrev sourceOpen := IntegralTwoChartNormalization318.sourceOpen R a (arithmeticDenominator R d)
  (OpenOrder R a d)
@[expose] def point : Spec (CommRingCat.of K) ⟶ model R a d :=
  Spec.map (CommRingCat.ofHom (openMap R K a d t hd ht hn z hz)) ≫ sourceOpen R a d

theorem point_over_base : point R K a d t hd ht hn z hz ≫ structureMap R a d =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  unfold point structureMap IntegralTwoChartNormalization318.structureMap
  rw [Category.assoc, ←Category.assoc (sourceOpen R a d),
    IntegralTwoChartNormalization318.factorization,
    IntegralTwoChartNormalization318.finite_factor, Category.assoc,
    JLineAtlas318.chart_over_base, ←Spec.map_comp, ←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change openMap R K a d t hd ht hn z hz
    (algebraMap (Base R a d) (OpenOrder R a d)
      (algebraMap R[X] (Base R a d) (C r))) = algebraMap R K r
  rw [openMap_base, baseEvaluation_polynomial, Polynomial.aeval_C]

/-- Properness supplies a section of the actual normal model with exactly
the prescribed entire field point, including all four signed roots. -/
theorem exists_center (hN : arithmeticDenominator R d ≠ 0) :
    ∃ g : Spec (CommRingCat.of R) ⟶ model R a d,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g = point R K a d t hd ht hn z hz ∧
      g ≫ structureMap R a d = 𝟙 _ := by
  letI : IsProper (structureMap R a d) :=
    IntegralTwoChartNormalization318.proper_model R a (arithmeticDenominator R d) (OpenOrder R a d) hN
  have hproper : IsProper (structureMap R a d) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  have hv : ValuativeCriterion (structureMap R a d) := hproper.1.1.1
  let S : ValuativeCommSq (structureMap R a d) :=
    { R := R, K := K, i₁ := point R K a d t hd ht hn z hz, i₂ := 𝟙 _
      commSq := ⟨by simpa only [Category.comp_id] using point_over_base R K a d t hd ht hn z hz⟩ }
  obtain ⟨g,hg,hb⟩ := (hv.existence S).exists_lift
  exact ⟨g,hg,hb⟩
end IntegralNormalPointCenter318
