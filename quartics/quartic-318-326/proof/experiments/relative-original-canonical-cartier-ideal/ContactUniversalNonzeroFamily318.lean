module
public import ContactRelativeOriginalSmoothProper318
public import ContactUniversalZeroFinitePresentation318
public import ContactUniversalNonzeroLocus318
public section
noncomputable section
namespace ContactUniversalNonzeroFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "S" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz

/-- The actual universal zero family is proper over the parameter scheme,
not merely closed over its ambient curve. -/
instance projection_proper : IsProper π := by
  unfold ContactUniversalGlobalZero318.projection
  infer_instance
instance projection_finitePresentation : LocallyOfFinitePresentation π := by
  unfold ContactUniversalGlobalZero318.projection
  infer_instance

/-- Restrict the SAME universal zero family to the explicit nonzero-section
parameter open. This removes the zero section geometrically, not by an
extra nonvanishing premise attached to an unchanged parameter scheme. -/
abbrev base : Scheme := W.toScheme
abbrev scheme : Scheme := pullback π W.ι
abbrev projection : scheme R c L hz ⟶ base R c L hz := pullback.snd π W.ι
@[expose] def toUniversal : scheme R c L hz ⟶ ContactUniversalGlobalZero318.scheme R c L hz :=
  pullback.fst π W.ι

lemma square : IsPullback (toUniversal R c L hz) (projection R c L hz) π W.ι :=
  .of_hasPullback _ _
instance proper : IsProper (projection R c L hz) := inferInstance
instance finitePresentation : LocallyOfFinitePresentation (projection R c L hz) := inferInstance

/-- The SAME ambient curve restricted to the SAME parameter open.
Smoothness supplies genuine ambient flatness for the next relative step. -/
abbrev ambient : Scheme := pullback (ContactRelativeStructuralHOne318.projection S c) W.ι
abbrev ambientProjection : ambient R c L hz ⟶ base R c L hz :=
  pullback.snd (ContactRelativeStructuralHOne318.projection S c) W.ι
instance ambient_smooth : Smooth (ambientProjection R c L hz) := inferInstance
instance ambient_proper : IsProper (ambientProjection R c L hz) := inferInstance

/-- Precise completed inputs: actual nonzero parameter restriction, proper
finitely presented zero family, and smooth proper ambient family. Flatness
of the ZERO projection is deliberately not inferred from these facts. -/
theorem properties : IsProper (projection R c L hz) ∧
    LocallyOfFinitePresentation (projection R c L hz) ∧
    Smooth (ambientProjection R c L hz) ∧ IsProper (ambientProjection R c L hz) :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance⟩
end ContactUniversalNonzeroFamily318
