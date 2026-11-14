module
public import LegendrePeriodScalingHolomorph318
public section
noncomputable section
namespace LegendreActualTorus318
open ComplexAffineFreeTranslation318 LegendreActualPeriodScaling318
open scoped Topology Manifold ContDiff
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)]
@[expose] def periods : AddSubgroup ℂ:=LegendreModularPeriodLattice318.lattice (parameter l)
instance periods_discrete : DiscreteTopology (periods l):=
  LegendreModularPeriodLattice318.lattice_discrete (parameter l)
instance quotient_compact : CompactSpace (Torus (periods l)):=
  LegendreModularPeriodLattice318.torus_compact (parameter l)
local instance : ChartedSpace ℂ (Torus (periods l)):=ComplexLineLatticeAtlas318.chartedSpace (periods l)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus (periods l)):=ComplexLineLatticeAtlas318.complex_manifold (periods l)
local instance : ChartedSpace ℂ (OriginalPeriodPlaneOverlap318.CompletedPlane (periods l)):=
  OriginalPeriodCompletedComplexAtlas318.chartedSpace (periods l)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane (periods l)):=
  OriginalPeriodCompletedComplexAtlas318.complex_manifold (periods l)
local instance : ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane l):=
  LegendreCompletedComplexAtlas318.chartedSpace l
local instance : IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane l):=
  LegendreCompletedComplexAtlas318.complex_manifold l

/-- A genuine PRODUCED period quotient and its full biholomorphism to
the independent completed Legendre curve. This uses actual modular
j-surjectivity, exact lattice-sum normalization, concrete scaling on
both native charts, and the actual original Weierstrass map. -/
@[expose] def comparison : Torus (periods l)≃ₜLegendrePlaneOverlap318.CompletedPlane l :=
  (OriginalPeriodIndependentBiholomorph318.comparison (periods l)).trans
    (LegendrePeriodScalingHolomorph318.comparison (periods l) l (scaling l)
      (scaling_spec l).1 (scaling_spec l).2)
theorem biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison l) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison l).symm := by
  have hp:=OriginalPeriodIndependentBiholomorph318.biholomorphic (periods l)
  have hs:=LegendrePeriodScalingHolomorph318.biholomorphic (periods l) l (scaling l)
    (scaling_spec l).1 (scaling_spec l).2
  exact ⟨hs.1.comp hp.1,hp.2.comp hs.2⟩
lemma origin : comparison l 0=LegendrePlaneOverlap318.infinityChart l (LegendrePlaneOverlap318.origin l) := by
  change LegendrePeriodScalingPoints318.equivalence (periods l) l (scaling l)
    (scaling_spec l).1 (scaling_spec l).2 (OriginalPeriodIndependentBiholomorph318.comparison (periods l) 0)=_
  rw [OriginalPeriodIndependentBiholomorph318.actual_origin,
    LegendrePeriodScalingPoints318.origin_value]
lemma actual_finite (q:Torus (periods l)) (hq:q≠0) :
    comparison l q=LegendrePlaneOverlap318.finiteChart l
      (LegendrePeriodScalingPoints318.finite (periods l) l (scaling l)
        (scaling_spec l).1 (scaling_spec l).2
        (OriginalPeriodCompletedPointIdentification318.originalFinite (periods l) ⟨q,hq⟩)) := by
  change LegendrePeriodScalingPoints318.equivalence (periods l) l (scaling l)
    (scaling_spec l).1 (scaling_spec l).2 (OriginalPeriodIndependentBiholomorph318.comparison (periods l) q)=_
  rw [OriginalPeriodIndependentBiholomorph318.actual_finite _ q hq,
    LegendrePeriodScalingPoints318.finite_value]
lemma actual_scheme_finite (q:Torus (periods l)) (hq:q≠0) :
    LegendreCompletedPointIdentification318.schemeEquivalence l (comparison l q)=
      CompletedFieldPoints318.finiteInclusion (NormalizedLegendreProjectiveModel318.A l)
        (NormalizedLegendreProjectiveModel318.B l)
        (LegendreCompletedPointIdentification318.finiteScheme l
          (LegendrePeriodScalingPoints318.finite (periods l) l (scaling l)
            (scaling_spec l).1 (scaling_spec l).2
            (OriginalPeriodCompletedPointIdentification318.originalFinite (periods l) ⟨q,hq⟩))) := by
  rw [actual_finite l q hq,LegendreCompletedPointIdentification318.scheme_finite]
end LegendreActualTorus318
