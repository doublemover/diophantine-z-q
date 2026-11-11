module
public import IntegralProperBicanonicalModel318
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace IntegralOriginalSmoothCharts318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- Each original contact chart is smooth over the original base: the
ramified root is a polynomial coordinate, its principal localization is
smooth, and the remaining three root factors are genuinely étale. -/
theorem branch_smooth (h2 : IsUnit (2:R)) (i : Fin 4) :
    Algebra.Smooth R (OpenOrder R c i) := by
  letI : Algebra.Smooth R R[X] := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth R (BranchBase R c i) :=
    Algebra.Smooth.of_equiv
      (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).symm
  letI : Algebra.Smooth (BranchBase R c i) (OpenBase R c i) :=
    Algebra.Smooth.of_isLocalization_Away (IntegralBranchChart318.denominator
      (c i) (contacts R i) (otherTwist R c i) (otherContact R i))
  letI : Algebra.Smooth R (OpenBase R c i) :=
    Algebra.Smooth.comp R (BranchBase R c i) (OpenBase R c i)
  letI : Algebra.Etale (OpenBase R c i) (OpenOrder R c i) :=
    (finite_free_etale R c h2 i).2.2
  exact Algebra.Smooth.comp R (OpenBase R c i) (OpenOrder R c i)

/-- Smoothness of the SAME principal localizations of the original source,
via their actual coefficient-preserving branch equivalences. -/
theorem source_branch_smooth (h2 : IsUnit (2:R)) (i : Fin 4) :
    Algebra.Smooth R (IntegralBranchCoordinates318.B R c i) := by
  letI := branch_smooth R c h2 i
  exact Algebra.Smooth.of_equiv (IntegralBranchLocalization318.sourceLocalizationEquiv R c i).symm

/-- The whole original finite source is smooth on the exact good base;
coverage uses the original separation integer and all four branch ideals. -/
theorem whole_source_smooth (h2 : IsUnit (2:R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    Algebra.Smooth R (SourceOrder R c) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget (algebraMap R (SourceOrder R c))
    (Set.range (IntegralBranchDenominatorCover318.denominator R c))
    (IntegralBranchDenominatorCover318.span_top R c hN)
  rintro ⟨d,⟨i,rfl⟩⟩
  letI := source_branch_smooth R c h2 i
  simpa only [IsScalarTower.algebraMap_eq R (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c i)] using
      RingHom.smooth_algebraMap.mpr (source_branch_smooth R c h2 i)

/-- The ACTUAL infinity order is smooth over the original base using its
reciprocal-root coordinate presentation, not a ramified base coordinate. -/
theorem infinity_smooth (h2 : IsUnit (2:R)) :
    Algebra.Smooth R (IntegralInfinityChart318.Order R c) := by
  letI : Algebra.Smooth R R[X] := ⟨inferInstance,inferInstance⟩
  letI : Algebra.Smooth R[X] (IntegralInfinityChart318.Base R c) :=
    Algebra.Smooth.of_isLocalization_Away (IntegralInfinityChart318.denominator R c)
  letI : Algebra.Smooth R (IntegralInfinityChart318.Base R c) :=
    Algebra.Smooth.comp R R[X] (IntegralInfinityChart318.Base R c)
  letI : Algebra.Etale (IntegralInfinityChart318.Base R c) (IntegralInfinityChart318.Order R c) :=
    (IntegralInfinityChart318.finite_free_etale R c h2).2.2
  exact Algebra.Smooth.comp R (IntegralInfinityChart318.Base R c) (IntegralInfinityChart318.Order R c)
end IntegralOriginalSmoothCharts318
