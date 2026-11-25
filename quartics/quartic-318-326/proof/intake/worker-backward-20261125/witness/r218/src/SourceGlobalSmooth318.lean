module
public import SourceBranchLocalization318
public import Mathlib.RingTheory.RingHom.Smooth
public section
noncomputable section
namespace SourceGlobalSmooth318
open SourceFiniteBranch318
open Polynomial
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)

lemma chart_smooth (i:Fin 4) : Algebra.Smooth ℚ (OpenOrder c i):=by
  letI:Algebra.Smooth ℚ ℚ[X]:=⟨inferInstance,inferInstance⟩
  letI:Algebra.Smooth ℚ (BranchBase c i):=
    Algebra.Smooth.of_equiv (LinearRootCoordinate318.coordinateEquiv (c i)
      (LinearContactSquareclass318.contacts i)).symm
  letI:Algebra.Smooth ℚ (OpenBase c i):=Algebra.Smooth.comp ℚ (BranchBase c i) (OpenBase c i)
  letI:Algebra.Etale (OpenBase c i) (OpenOrder c i):=(source_finite_branch c i).2.2.1
  exact Algebra.Smooth.comp ℚ (OpenBase c i) (OpenOrder c i)

lemma localized_smooth (i:Fin 4) :
    Algebra.Smooth ℚ (Localization.Away (SourceDenominatorCover318.denominator c i)):=by
  letI:=chart_smooth c i
  exact Algebra.Smooth.of_equiv (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm

/-- The entire original four-contact polynomial order is smooth over Q.
The four actual branch localizations cover it by a proved partition of unity. -/
theorem source_smooth : Algebra.Smooth ℚ (ContactKummerOrder318.SourceOrder c):=by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget
    (algebraMap ℚ (ContactKummerOrder318.SourceOrder c))
    (Set.range (SourceDenominatorCover318.denominator c)) (SourceDenominatorCover318.span_top c)
  rintro ⟨d,⟨i,rfl⟩⟩
  letI:=localized_smooth c i
  simpa only [IsScalarTower.algebraMap_eq ℚ (ContactKummerOrder318.SourceOrder c)
    (Localization.Away (SourceDenominatorCover318.denominator c i))] using
    (RingHom.smooth_algebraMap.mpr (localized_smooth c i))

end SourceGlobalSmooth318
