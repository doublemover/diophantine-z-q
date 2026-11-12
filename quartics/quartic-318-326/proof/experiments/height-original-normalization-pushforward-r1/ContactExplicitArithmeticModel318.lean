module
public import ContactArithmeticBaseCoverage318
public import IntegralGlobalLocalCompletion318
public section
noncomputable section
namespace ContactExplicitArithmeticModel318
open AlgebraicGeometry CategoryTheory Ring
open ContactArithmeticDenominator318 ContactArithmeticBase318 ContactArithmeticTwists318
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The original model over its explicitly constructed arithmetic base. -/
abbrev Model := IntegralGluedModel318.scheme (Base c) (twist c)
abbrev tensor := IntegralGlobalBicanonicalPair318.tensor (Base c) (twist c)
@[expose] def q := IntegralGlobalBicanonicalPair318.q (Base c) (twist c) (separation_unit c)
@[expose] def pencil := IntegralSectionProjectiveMap318.projectiveMap
  (Base c) (twist c) (separation_unit c)
@[expose] def pulledLine := IntegralPencilPulledCoordinates318.line
  (Base c) (twist c) (separation_unit c)

/-- No normality, Noetherianity, base injection or good-prime-unit premise
is now supplied by the caller: all belong to the explicit Z[1/denominator]. -/
theorem smooth_proper :
    Smooth (IntegralGluedModel318.structureMap (Base c) (twist c)) ∧
    IsProper (IntegralGluedModel318.structureMap (Base c) (twist c)) ∧
    IsSeparated (IntegralGluedModel318.structureMap (Base c) (twist c)) := by
  have h := IntegralSmoothProperBicanonical318.model_and_original_pair
    (Base c) (twist c) (separation_unit c)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem finite_flat : IsFinite (pencil c) ∧ Flat (pencil c) :=
  IntegralOriginalFiniteFlatPencil318.section_pencil_finite_flat
    (Base c) (twist c) (separation_unit c)

/-- Actual pullback O(1) identified with the actual original tensor sheaf,
with the already checked exact section normalization. -/
@[expose] def lineIso : pulledLine c ≅ tensor c :=
  IntegralPencilLineComparison318.iso (Base c) (twist c) (separation_unit c)
theorem first_section : (lineIso c).hom.app ⊤
    (IntegralPencilPulledCoordinates318.q0 (Base c) (twist c) (separation_unit c))=q c 0 :=
  IntegralPencilLineComparison318.q0_normalized (Base c) (twist c) (separation_unit c)
theorem second_section : (lineIso c).hom.app ⊤
    (IntegralPencilPulledCoordinates318.q1 (Base c) (twist c) (separation_unit c))=q c 1 :=
  IntegralPencilLineComparison318.q1_normalized (Base c) (twist c) (separation_unit c)

abbrev Stalk (x : Model c) := (Model c).presheaf.stalk x
instance stalk_domain (x : Model c) : IsDomain (Stalk c x) :=
  IntegralGlobalHeightOne318.stalk_domain (Base c) (twist c) (algebraMap_injective c) x

/-- Every actual intrinsic codimension-one stalk of this explicitly chosen
arithmetic model is a DVR, including the original infinity locus. -/
theorem stalk_dvr (x : Model c) (hx : ringKrullDim (Stalk c x)=1) :
    IsDiscreteValuationRing (Stalk c x) :=
  IntegralGlobalHeightOne318.stalk_dvr (Base c) (twist c) (algebraMap_injective c)
    (two_unit c) (separation_unit c) x hx

variable (x : Model c) (hx : ringKrullDim (Stalk c x)=1)
local instance actualDVR : IsDiscreteValuationRing (Stalk c x) := stalk_dvr c x hx
abbrev Completion :=
  letI := stalk_dvr c x hx
  ActualDVRCompletion318.Completion (Stalk c x)
theorem completion_injective : Function.Injective
    (algebraMap (Stalk c x) (Completion c x hx)) :=
  ActualDVRCompletion318.completion_injective (Stalk c x)
theorem completion_faithfullyFlat :
    Module.FaithfullyFlat (Stalk c x) (Completion c x hx) :=
  CompletionDescent318.completion_faithfullyFlat (Stalk c x)
theorem completion_value (a : Stalk c x) :
    IsDiscreteValuationRing.addVal (Completion c x hx)
      (algebraMap (Stalk c x) (Completion c x hx) a)=
        IsDiscreteValuationRing.addVal (Stalk c x) a :=
  ActualDVRCompletion318.completion_value (Stalk c x) a
end ContactExplicitArithmeticModel318
