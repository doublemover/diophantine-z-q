module
public import ReesHomogeneousCharts318
public import OriginalPrimeThreeLocalFirstUReesQuotient318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public section
noncomputable section
namespace OriginalPrimeThreeNativeReesProj318
open AlgebraicGeometry CategoryTheory
open ReesNativeGrading318 ReesIdealRatioImage318
open OriginalPrimeThreeLocalizedCotangent318 OriginalPrimeThreeActualRootEquations318

abbrev Center := IsLocalRing.maximalIdeal PointRing
abbrev ReesRing := reesAlgebra Center
abbrev grading := grade Center

/-- Native Proj of the literally graded Rees algebra of the actual
normalized local maximal ideal. It is not asserted to be regular. -/
abbrev actualReesProj : Scheme := Proj grading

@[expose] def generator (j : Fin 3) : ReesRing :=
  degreeOne Center ⟨pointRoot j.succ, localRoot_mem_maximal j⟩

theorem generator_mem (j : Fin 3) : generator j ∈ grading 1 :=
  degreeOne_mem Center ⟨pointRoot j.succ, localRoot_mem_maximal j⟩

abbrev NativeChart (j : Fin 3) := HomogeneousLocalization.Away grading (generator j)
abbrev NativeOverlap (j k : Fin 3) :=
  HomogeneousLocalization.Away grading (generator j * generator k)

/-- The structure morphism has the actual PointRing as base. The
degree-zero identification was proved, not assumed. -/
@[expose] def toPointSpec : actualReesProj ⟶ Spec (CommRingCat.of PointRing) :=
  Proj.toSpecZero grading ≫
    Spec.map (CommRingCat.ofHom (zeroPieceEquiv Center).symm.toRingHom)

/-- Exact native affine chart on the actual native Rees Proj. This does
not yet identify its ring with the separate explicit retained-root chart. -/
@[expose] def nativeChartIso (j : Fin 3) :
    (Proj.basicOpen grading (generator j)).toScheme ≅ Spec (CommRingCat.of (NativeChart j)) :=
  Proj.basicOpenIsoSpec grading (generator j) (generator_mem j) (by decide)

@[expose] def nativeChartInclusion (j : Fin 3) :
    Spec (CommRingCat.of (NativeChart j)) ⟶ actualReesProj :=
  Proj.awayι grading (generator j) (generator_mem j) (by decide)

instance nativeChart_openImmersion (j : Fin 3) : IsOpenImmersion (nativeChartInclusion j) := by
  dsimp only [nativeChartInclusion]
  infer_instance

@[expose] def nativeOverlapMap (j k : Fin 3) :
    NativeChart j →+* NativeOverlap j k :=
  HomogeneousLocalization.awayMap grading (generator_mem k) rfl

/-- Native scheme-theoretic intersection, with the actual Proj
inclusions. This is not an asserted gluing of the old explicit charts. -/
@[expose] def nativeOverlapIso (j k : Fin 3) :
    Limits.pullback (nativeChartInclusion j) (nativeChartInclusion k) ≅
      Spec (CommRingCat.of (NativeOverlap j k)) :=
  Proj.pullbackAwayιIso grading (generator_mem j) (by decide)
    (generator_mem k) (by decide) rfl

theorem nativeOverlapMap_compatibility (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (nativeOverlapMap j k)) ≫ nativeChartInclusion j =
      Proj.awayι grading (generator j * generator k)
        (SetLike.mul_mem_graded (generator_mem j) (generator_mem k)) (by decide) :=
  Proj.SpecMap_awayMap_awayι grading (generator_mem j) (by decide)
    (generator_mem k) rfl

end OriginalPrimeThreeNativeReesProj318
