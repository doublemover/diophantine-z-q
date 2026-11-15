module
public import FourRootDualParameterBaseChange318
public import FourRootRatioIntegralSections318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace FourRootRatioPuncturedSections318
open FourRootRatioOrder318 FourRootRatioGenericEquiv318 FourRootIntegralDuality318
open FourRootRatioIntegralSections318 FiniteDualTransport318
variable {R : Type*} [CommRing R] (q : R) (r : Fin 3 → R)
abbrev GenericBase := Localization.Away q
local notation "S" => GenericBase q
@[expose] def genericQ : S := algebraMap R S q
@[expose] def genericRatios (i : Fin 3) : S := algebraMap R S (r i)
lemma generic_unit : IsUnit (genericQ q) := IsLocalization.Away.algebraMap_isUnit (S:=S) q

lemma original_parameters (i : Fin 4) :
    algebraMap R S (original q r i)=original (genericQ q) (genericRatios q r) i := by
  refine Fin.cases rfl (fun i => ?_) i
  exact map_mul _ _ _
lemma ratio_parameters (i : Fin 4) :
    algebraMap R S (normalized q r i)=normalized (genericQ q) (genericRatios q r) i := by
  refine Fin.cases rfl (fun _ => rfl) i

@[expose] def originalExtension := FourRootDualParameterBaseChange318.squareMap
  (original q r) (original (genericQ q) (genericRatios q r)) (original_parameters q r)
@[expose] def ratioExtension := FourRootDualParameterBaseChange318.squareMap
  (normalized q r) (normalized (genericQ q) (genericRatios q r)) (ratio_parameters q r)
@[expose] def genericEquiv := equiv (genericQ q) (genericRatios q r) (generic_unit q)

variable (h : Rˣ) (s c : R) (he : q=(h:R)*s)
@[expose] def genericUnit : Sˣ := Units.map (algebraMap R S) h
include he in
lemma generic_factor : genericQ q=(genericUnit q h:S)*algebraMap R S s := by
  change algebraMap R S q = algebraMap R S (h:R)*algebraMap R S s
  rw [he,map_mul]
lemma coefficient0_map : algebraMap R S (coefficient0 h s c)=
    coefficient0 (genericUnit q h) (algebraMap R S s) (algebraMap R S c) := by
  change algebraMap R S (c*(↑h⁻¹:R)^3*s) =
    algebraMap R S c*(algebraMap R S (↑h⁻¹:R))^3*algebraMap R S s
  rw [map_mul,map_mul,map_pow]
lemma coefficient1_map : algebraMap R S (coefficient1 h c)=
    coefficient1 (genericUnit q h) (algebraMap R S c) := by
  change algebraMap R S (c*(↑h⁻¹:R)^3) =
    algebraMap R S c*(algebraMap R S (↑h⁻¹:R))^3
  rw [map_mul,map_pow]

include he in
/-- Actual punctured-base comparison: BOTH maps originate from the full
integral dual tensor modules. The required generic unit is PRODUCED by the
specified localization, not left as an unproved nonvanishing premise. -/
lemma section0_comparison :
    squareTransport (genericEquiv q r)
      (originalExtension q r
        (squareFrame (frame (original q r)) (algebraMap R (OriginalOrder q r) (c*s^4)))) =
    ratioExtension q r
      (squareFrame (frame (normalized q r)) (algebraMap R (RatioOrder q r) (coefficient0 h s c))) := by
  rw [originalExtension,ratioExtension,FourRootDualParameterBaseChange318.squareMap_scalar,
    FourRootDualParameterBaseChange318.squareMap_scalar]
  simp only [map_mul,map_pow]
  rw [coefficient0_map]
  exact section0_image (genericUnit q h) (algebraMap R S s) (algebraMap R S c)
    (genericQ q) (genericRatios q r) (generic_unit q) (generic_factor q h s he)

include he in
lemma section1_comparison :
    squareTransport (genericEquiv q r)
      (originalExtension q r
        (squareFrame (frame (original q r)) (algebraMap R (OriginalOrder q r) (c*s^3)))) =
    ratioExtension q r
      (squareFrame (frame (normalized q r)) (algebraMap R (RatioOrder q r) (coefficient1 h c))) := by
  rw [originalExtension,ratioExtension,FourRootDualParameterBaseChange318.squareMap_scalar,
    FourRootDualParameterBaseChange318.squareMap_scalar]
  simp only [map_mul,map_pow]
  rw [coefficient1_map]
  exact section1_image (genericUnit q h) (algebraMap R S s) (algebraMap R S c)
    (genericQ q) (genericRatios q r) (generic_unit q) (generic_factor q h s he)
end FourRootRatioPuncturedSections318
