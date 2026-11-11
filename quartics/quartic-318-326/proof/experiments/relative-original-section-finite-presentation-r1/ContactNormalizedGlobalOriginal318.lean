module
public import ContactNormalizedGlobalFiniteFlat318
public section
noncomputable section
namespace ContactNormalizedGlobalOriginal318
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
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "p" i => ContactNormalizedChartZeroFamily318.projection R c L hz i
local notation "u" => ProjectiveParameterSliceGluing318.into R P
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "proj" => ContactNormalizedZeroTransitions318.projection R c L hz
local notation "t" => ContactNormalizedZeroTransitions318.transition R c L hz

/-- The actual global zero family retains its original contact-curve
map, obtained by gluing the SAME chart maps used in the overlap cycle. -/
@[expose] def original : ContactNormalizedGlobalZero318.scheme R c L hz ⟶ curve R c := by
  fapply Multicoequalizer.desc
  · exact ContactNormalizedOriginalCurve318.chart R c L hz
  rintro ⟨i,j⟩
  change inc i j ≫ ContactNormalizedOriginalCurve318.chart R c L hz i=
    ((t i j).hom ≫ inc j i) ≫ ContactNormalizedOriginalCurve318.chart R c L hz j
  rw [Category.assoc,ContactZeroOverlapOriginal318.transition]
@[reassoc] lemma into_original (i : Fin F.size) :
    ContactNormalizedGlobalZero318.into R c L hz i ≫ original R c L hz=
      ContactNormalizedOriginalCurve318.chart R c L hz i :=
  Multicoequalizer.π_desc _ _ _ _ _
end ContactNormalizedGlobalOriginal318
