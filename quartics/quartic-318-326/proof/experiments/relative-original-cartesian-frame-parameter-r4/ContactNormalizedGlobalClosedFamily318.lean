module
public import ContactNormalizedGlobalRelative318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace ContactNormalizedGlobalClosedFamily318
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

local notation "π" => ContactNormalizedZeroProjection318.projection R c L hz
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "a" => ContactNormalizedGlobalOriginal318.original R c L hz

/-- The ORIGINAL curve over the ACTUAL normalized-section parameter. -/
abbrev ambient : Scheme := pullback q b
abbrev ambientProjection : ambient R c L hz ⟶ ContactNormalizedSectionParameter318.scheme R c L hz :=
  pullback.snd q b
instance ambient_proper : IsProper (ambientProjection R c L hz) := inferInstance
instance ambient_smooth : Smooth (ambientProjection R c L hz) := inferInstance

/-- Actual morphism into the original relative curve, retaining BOTH
previously constructed global projection maps. -/
@[expose] def into : ContactNormalizedGlobalZero318.scheme R c L hz ⟶ ambient R c L hz :=
  pullback.lift a π (ContactNormalizedGlobalRelative318.square R c L hz)
@[reassoc] lemma into_original : into R c L hz ≫ pullback.fst q b=a := pullback.lift_fst ..
@[reassoc] lemma into_projection : into R c L hz ≫ ambientProjection R c L hz=π :=
  pullback.lift_snd ..

instance mono : Mono (into R c L hz) := ⟨by
  intro X v w h
  apply ContactNormalizedGlobalJointMono318.hom_ext R c L hz v w
  · have hh := congrArg (fun k => k ≫ pullback.fst q b) h
    simpa only [Category.assoc,into_original] using hh
  · have hh := congrArg (fun k => k ≫ ambientProjection R c L hz) h
    simpa only [Category.assoc,into_projection] using hh⟩

/-- Finiteness of the genuine zero projection and separatedness of the
original ambient curve make this actual ambient morphism finite. -/
instance finite : IsFinite (into R c L hz) := by
  haveI : IsFinite (into R c L hz ≫ ambientProjection R c L hz) := by
    rw [into_projection]
    infer_instance
  exact IsFinite.of_comp (into R c L hz) (ambientProjection R c L hz)

/-- The globally descended family is a genuine CLOSED SUBSCHEME of the
original relative curve, not merely a finite-flat abstract scheme with a
map to the parameter. Its ideal and relative Cartier description can now
be taken for this exact embedding. -/
instance closed : IsClosedImmersion (into R c L hz) :=
  (IsClosedImmersion.iff_isFinite_and_mono (into R c L hz)).mpr ⟨inferInstance,inferInstance⟩
end ContactNormalizedGlobalClosedFamily318
