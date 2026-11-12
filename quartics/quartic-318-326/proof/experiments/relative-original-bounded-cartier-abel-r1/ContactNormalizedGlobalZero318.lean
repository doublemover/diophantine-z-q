module
public import ContactZeroTripleLeg318
public section
noncomputable section
namespace ContactNormalizedGlobalZero318
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

/-- Full original ZERO-FAMILY gluing data on the actual normalized
section parameter charts. Every overlap, transition, self identity,
triple leg and cycle is constructed from the original zero schemes. -/
@[expose] def data : Scheme.GlueData where
  J := Fin F.size
  U := ContactNormalizedChartZeroFamily318.scheme R c L hz
  V := fun ij => ContactNormalizedZeroTransitions318.overlap R c L hz ij.1 ij.2
  f := ContactNormalizedZeroTransitions318.inclusion R c L hz
  f_id := fun i => ContactZeroOverlapJointMono318.inclusion_self R c L hz i
  t := fun i j => (ContactNormalizedZeroTransitions318.transition R c L hz i j).hom
  t_id := ContactZeroOverlapJointMono318.transition_self R c L hz
  t' := ContactZeroTripleTransition318.transition R c L hz
  t_fac := ContactZeroTripleLeg318.leg R c L hz
  cocycle := ContactZeroTripleTransition318.cycle R c L hz
  f_open := fun i j => inferInstance

/-- Actual global zero scheme glued from the original finite-flat chart
families. The global map to the normalized parameter and its finite-flat
properties are subsequent descent statements, not inferred by this name. -/
abbrev scheme : Scheme := (data R c L hz).glued
abbrev into (i : Fin F.size) : ContactNormalizedChartZeroFamily318.scheme R c L hz i ⟶
    scheme R c L hz := (data R c L hz).ι i
instance into_open (i : Fin F.size) : IsOpenImmersion (into R c L hz i) := inferInstance
abbrev cover : (scheme R c L hz).OpenCover := (data R c L hz).openCover
lemma jointly_surjective (x : scheme R c L hz) : ∃ i y,into R c L hz i y=x :=
  (data R c L hz).ι_jointly_surjective x
end ContactNormalizedGlobalZero318
