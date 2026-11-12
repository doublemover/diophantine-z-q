module
public import ProjectiveParameterSliceNonzero318
public import ContactNormalizedSectionParameter318
public import ContactUniversalNonzeroFinite318
public section
noncomputable section
namespace ContactNormalizedChartZeroFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
local notation "π" => ContactUniversalNonzeroFamily318.projection R c L hz
local instance : IsFinite π := ContactUniversalNonzeroFinite318.finite R c L hz
local instance : Flat π := ContactUniversalNonzeroFlat318.flat R c L hz

@[expose] def parameterMap (i : Fin F.size) :
    ProjectiveParameterSliceSchemes318.chart R Γ(L.object,⊤) i ⟶
      ContactUniversalNonzeroFamily318.base R c L hz :=
  ProjectiveParameterSliceNonzero318.intoNonzero R Γ(L.object,⊤) i

/-- The SAME original finite-flat universal zero family, restricted to
an actual normalized parameter chart through its proved nonzero factor.
This is not a separately guessed zero family or a fiberwise substitute. -/
abbrev scheme (i : Fin F.size) : Scheme := pullback π (parameterMap R c L hz i)
abbrev projection (i : Fin F.size) : scheme R c L hz i ⟶
    ProjectiveParameterSliceSchemes318.chart R Γ(L.object,⊤) i :=
  pullback.snd π (parameterMap R c L hz i)
instance finite (i : Fin F.size) : IsFinite (projection R c L hz i) := inferInstance
instance flat (i : Fin F.size) : Flat (projection R c L hz i) := inferInstance
instance finitePresentation (i : Fin F.size) : LocallyOfFinitePresentation (projection R c L hz i) :=
  inferInstance

/-- Every affine chart of the ACTUAL original normalized-section
parameter now carries the actual finite-flat zero family. Compatibility
and descent across its unit-normalized overlaps remain the next step. -/
theorem properties (i : Fin F.size) : IsFinite (projection R c L hz i) ∧
    Flat (projection R c L hz i) ∧ LocallyOfFinitePresentation (projection R c L hz i) :=
  ⟨inferInstance,inferInstance,inferInstance⟩
end ContactNormalizedChartZeroFamily318
