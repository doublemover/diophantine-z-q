module
public import OriginalInfinityRatioMap318
public import FourRootRatioIntegralSections318
public import NormalizedDualBicanonicalSections318
public section
noncomputable section
namespace OriginalInfinityRatioSections318
open Polynomial OriginalInfinityRatioParameters318 FourRootRatioOrder318
open FourRootIntegralDuality318 FiniteDualTransport318
variable (V : Type*) [CommRing V] (d a : Fin 4 → V)
local notation "R" => Base V d a
local notation "q" => common V d a
local notation "r" => ratios V d a
@[expose] def scalar : R := algebraMap V[X] R (C (NormalizedDualBicanonicalSections318.sectionCoefficient V d))
@[expose] def coefficient0 : R :=
  FourRootRatioIntegralSections318.coefficient0 (denominatorUnit V d a) (coordinate V d a) (scalar V d a)
@[expose] def coefficient1 : R :=
  FourRootRatioIntegralSections318.coefficient1 (denominatorUnit V d a) (scalar V d a)

/-- Actual integral sections of the ratio-order finite dual tensor module;
they exist BEFORE localizing the ramified coordinate or2. -/
@[expose] def section0 : Square (R:=R) (A:=RatioOrder q r) :=
  squareFrame (frame (normalized q r)) (algebraMap R (RatioOrder q r) (coefficient0 V d a))
@[expose] def section1 : Square (R:=R) (A:=RatioOrder q r) :=
  squareFrame (frame (normalized q r)) (algebraMap R (RatioOrder q r) (coefficient1 V d a))

lemma old_coefficient0 : algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity0 V d)=
    scalar V d a*(coordinate V d a)^4 := by
  simp only [NormalizedDualBicanonicalSections318.infinity0,map_mul,map_pow,scalar,coordinate]
lemma old_coefficient1 : algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity1 V d)=
    scalar V d a*(coordinate V d a)^3 := by
  simp only [NormalizedDualBicanonicalSections318.infinity1,map_mul,map_pow,scalar,coordinate]

lemma integral_identity0 : coefficient0 V d a*q^3=
    algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity0 V d) := by
  rw [coefficient0,common_eq,FourRootRatioIntegralSections318.coefficient0_identity,old_coefficient0]
lemma integral_identity1 : coefficient1 V d a*q^3=
    algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity1 V d) := by
  rw [coefficient1,common_eq,FourRootRatioIntegralSections318.coefficient1_identity,old_coefficient1]

/-- On ANY coefficient specialization where q is a unit, the genuine
whole generic dual-tensor transport has these exact integral images.
Existence of the sections themselves has no such localization premise. -/
lemma generic_section0 (hq : IsUnit q) :
    squareTransport (FourRootRatioGenericEquiv318.equiv q r hq)
      (squareFrame (frame (original q r))
        (algebraMap R (OriginalOrder q r)
          (algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity0 V d)))) = section0 V d a := by
  rw [old_coefficient0]
  exact FourRootRatioIntegralSections318.section0_image (denominatorUnit V d a)
    (coordinate V d a) (scalar V d a) q r hq (common_eq V d a)
lemma generic_section1 (hq : IsUnit q) :
    squareTransport (FourRootRatioGenericEquiv318.equiv q r hq)
      (squareFrame (frame (original q r))
        (algebraMap R (OriginalOrder q r)
          (algebraMap V[X] R (NormalizedDualBicanonicalSections318.infinity1 V d)))) = section1 V d a := by
  rw [old_coefficient1]
  exact FourRootRatioIntegralSections318.section1_image (denominatorUnit V d a)
    (coordinate V d a) (scalar V d a) q r hq (common_eq V d a)
end OriginalInfinityRatioSections318
