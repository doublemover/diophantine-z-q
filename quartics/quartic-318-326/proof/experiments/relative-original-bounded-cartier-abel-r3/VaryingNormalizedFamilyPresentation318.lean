module
public import VaryingNormalizedUniversalFamily318
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public section
noncomputable section
namespace VaryingNormalizedFamilyPresentation318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "Q" => VaryingNormalizedUniversalFamily318.quotient R A ι w
/-- Finite MODULE presentation comes from the actual original word basis.
It does not follow from finite flatness alone over arbitrary rings. -/
instance modulePresentation : Module.FinitePresentation N Q := by
  letI : Module.Finite N Q := Module.Finite.of_basis (VaryingNormalizedUniversalFamily318.basis R A ι w)
  letI : Module.Free N Q := Module.Free.of_basis (VaryingNormalizedUniversalFamily318.basis R A ι w)
  exact Module.finitePresentation_of_projective N Q
instance presentation : LocallyOfFinitePresentation
    (VaryingNormalizedUniversalFamily318.projection R A ι w) := by
  exact LocallyOfFinitePresentation.SpecMap_iff.mpr
    (RingHom.finitePresentation_algebraMap.mpr (inferInstanceAs (Algebra.FinitePresentation N Q)))
end VaryingNormalizedFamilyPresentation318
