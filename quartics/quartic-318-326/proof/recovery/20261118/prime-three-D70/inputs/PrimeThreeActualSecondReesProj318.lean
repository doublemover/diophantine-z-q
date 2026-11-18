module
public import PrimeThreeSelectedFirstUResidualCenter318
public import ReesDegreeOneGenerators318
public import ReesHomogeneousRatioEquiv318
public import HomogeneousAwayMapCocycle318
public section
noncomputable section
namespace PrimeThreeActualSecondReesProj318
open AlgebraicGeometry CategoryTheory
open PrimeThreeFirstUChartHomExt318 PrimeThreeFirstUResidualCenter318
open PrimeThreeSelectedFirstUResidualCenter318
open ReesNativeGrading318 ReesIdealRatioImage318
attribute [local instance] ReesHomogeneousRatioEquiv318.homogeneousBaseAlgebra

abbrev Center := localCenter
abbrev ReesRing := reesAlgebra Center
abbrev grading := grade Center
@[expose] def coordinate (i : Fin 3) : LocalU := chartToLocal (coordinates i)

theorem coordinate_mem (i : Fin 3) : coordinate i ∈ Center :=
  Ideal.mem_map_of_mem chartToLocal (PrimeThreeFirstUResidualCenter318.coordinate_mem i)

@[expose] def generator (i : Fin 3) : ReesRing := degreeOne Center ⟨coordinate i, coordinate_mem i⟩
theorem generator_mem (i : Fin 3) : generator i ∈ grading 1 :=
  degreeOne_mem Center ⟨coordinate i, coordinate_mem i⟩

/-- The actual second Rees Proj over the first-U open, centered at its
proved residual F9 maximal ideal. This is NOT yet a global second blowup
of the whole first-blowup scheme. -/
abbrev actualSecondProj : Scheme := Proj grading

@[expose] def toFirstU : actualSecondProj ⟶ Spec (CommRingCat.of LocalU) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom (zeroPieceEquiv Center).symm.toRingHom)

/-- Canonical morphism to the actual first-blowup scheme, through its
already proved arithmetic first-U open immersion. -/
@[expose] def toFirstBlowup : actualSecondProj ⟶
    OriginalPrimeThreeNativeReesProj318.actualReesProj :=
  toFirstU ≫ OriginalPrimeThreeFirstUNativeChart318.explicitFirstUInclusion

abbrev NativeChart (i : Fin 3) := HomogeneousLocalization.Away grading (generator i)
abbrev NativeOverlap (i j : Fin 3) :=
  HomogeneousLocalization.Away grading (generator i * generator j)
abbrev RatioChart (i : Fin 3) := ReesIdealRatioImage318.ratioAlgebra Center (coordinate i)

/-- These ratio rings embed in ambient localizations that invert only
u, first-U A, or first-U B respectively. The selected coordinate's inverse
need not lie in the ratio ring. Original u is not inverted on every chart. -/
@[expose] def nativeRatioEquiv (i : Fin 3) : NativeChart i ≃ₐ[LocalU] RatioChart i :=
  ReesHomogeneousRatioEquiv318.homogeneousRatioEquiv Center (coordinate i) (coordinate_mem i)

@[expose] def nativeChartIso (i : Fin 3) :
    (Proj.basicOpen grading (generator i)).toScheme ≅ Spec (CommRingCat.of (NativeChart i)) :=
  Proj.basicOpenIsoSpec grading (generator i) (generator_mem i) (by decide)

@[expose] def nativeChartInclusion (i : Fin 3) :
    Spec (CommRingCat.of (NativeChart i)) ⟶ actualSecondProj :=
  Proj.awayι grading (generator i) (generator_mem i) (by decide)

instance nativeChart_openImmersion (i : Fin 3) : IsOpenImmersion (nativeChartInclusion i) := by
  dsimp only [nativeChartInclusion]
  infer_instance

theorem native_generators_adjoin : Algebra.adjoin (grading 0) (Set.range generator) = ⊤ :=
  ReesDegreeOneGenerators318.adjoin_zero_generators_eq_top Center coordinate coordinate_mem localCenter_span

theorem native_second_chart_cover : (⨆ i : Fin 3, Proj.basicOpen grading (generator i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' grading generator (fun i => ⟨1, generator_mem i⟩) native_generators_adjoin

@[expose] def nativeOverlapMap (i j : Fin 3) : NativeChart i →+* NativeOverlap i j :=
  HomogeneousLocalization.awayMap grading (generator_mem j) rfl

@[expose] def nativeOverlapIso (i j : Fin 3) :
    Limits.pullback (nativeChartInclusion i) (nativeChartInclusion j) ≅
      Spec (CommRingCat.of (NativeOverlap i j)) :=
  Proj.pullbackAwayιIso grading (generator_mem i) (by decide)
    (generator_mem j) (by decide) rfl

abbrev NativeTriple (i j k : Fin 3) :=
  HomogeneousLocalization.Away grading ((generator i * generator j) * generator k)
@[expose] def nativeTripleMap (i j k : Fin 3) : NativeOverlap i j →+* NativeTriple i j k :=
  HomogeneousLocalization.awayMap grading (generator_mem k) rfl
@[expose] def nativeDirectTripleMap (i j k : Fin 3) : NativeChart i →+* NativeTriple i j k :=
  HomogeneousLocalization.awayMap grading
    (SetLike.mul_mem_graded (generator_mem j) (generator_mem k))
      (mul_assoc (generator i) (generator j) (generator k))

theorem native_second_triple_cocycle (i j k : Fin 3) :
    (nativeTripleMap i j k).comp (nativeOverlapMap i j) = nativeDirectTripleMap i j k :=
  HomogeneousAwayMapCocycle318.awayMap_comp grading (generator_mem i) (generator_mem j) (generator_mem k)

end PrimeThreeActualSecondReesProj318
