module
public import ActualTwoDescentInfinityPrimeSupportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOffOriginAffineCoverRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalCubicChartCover318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentOriginalPuncturedCharts318
variable {K : Type*} [Field K] [CharZero K]

/-- The full original affine chart covers EVERY scheme point except O.
The actual localization range, not a K-point calculation, supplies the lift. -/
theorem cover (n : K) (p : originalCubicScheme n) (hp : p≠infinityPoint n) :
    ∃ q,affineChart n q=p := by
  rcases actual_original_charts_cover n p with h|⟨q,hq⟩
  · exact h
  have hq0 : q.asIdeal≠originIdeal n := by
    intro he
    have heq : q=infinityPrime n := PrimeSpectrum.ext he
    apply hp
    rw [←hq,heq] <;> rfl
  have hv : chartV n ∉ q.asIdeal := by
    intro h
    exact hq0 ((ActualTwoDescentInfinityPrimeSupportRebuild318.support n q.asIdeal).mp h)
  have hm : q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (InfinityChart n) (InfinityPuncture n))) := by
    rw [PrimeSpectrum.localization_away_comap_range (InfinityPuncture n) (chartV n)]
    exact hv
  obtain ⟨r,hr⟩ := hm
  refine ⟨intoAffine n r,?_⟩
  calc
    affineChart n (intoAffine n r)=infinityChart n (intoInfinity n r) :=
      congrArg (fun f : overlapScheme n ⟶ originalCubicScheme n => f r)
        (pushout.condition (f:=intoAffine n) (g:=intoInfinity n))
    _=infinityChart n q := congrArg (infinityChart n) hr
    _=p := hq
end ActualTwoDescentOriginalOffOriginAffineCoverRebuild318
