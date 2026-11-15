module
public import ContactOriginalRationalFunctionConstants318
public import UniversalStructurePushforward318
public section
noncomputable section
namespace ContactOriginalUniversalFunctionConstants318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ)
local notation "p" => ContactOriginalRationalFunctionConstants318.projection c
variable {T : Scheme.{0}} (b : T ⟶ Spec (CommRingCat.of ℚ))
/-- Actual universal structural functions on every whole test. Flatness
is over Q, so this includes arbitrary nilpotent/nonaffine/noncompact T. -/
lemma structure_isIso : IsIso (UniversalStructurePushforward318.structureMorphism (pullback.snd p b)) := by
  letI : IsProper p := (ContactGlobalProper318.proper_integral_extension c).2.2
  letI := ContactOriginalRationalFunctionConstants318.appTop_isIso c
  exact UniversalStructurePushforward318.baseChange_structureMorphism_isIso p b
lemma app_isIso (U : T.Opens) : IsIso ((pullback.snd p b).app U) := by
  letI : IsProper p := (ContactGlobalProper318.proper_integral_extension c).2.2
  letI := ContactOriginalRationalFunctionConstants318.appTop_isIso c
  exact UniversalStructurePushforward318.baseChange_app_isIso p b U
lemma app_bijective (U : T.Opens) : Function.Bijective ((pullback.snd p b).app U) := by
  letI := app_isIso c b U
  exact ConcreteCategory.bijective_of_isIso _
end ContactOriginalUniversalFunctionConstants318
