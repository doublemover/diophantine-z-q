module
public import ContactNormalizedZeroTriple318
public import PullbackBaseIso318
public section
noncomputable section
namespace ContactNormalizedZeroTransitions318
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
local notation "p" k => ContactNormalizedChartZeroFamily318.projection R c L hz k
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "e" => ProjectiveParameterSliceSchemes318.transitionIso R P

/-- Literal open overlap of the SAME finite-flat zero chart. -/
abbrev overlap (i j : Fin F.size) : Scheme := pullback (p i) (inc i j)
@[expose] def inclusion (i j : Fin F.size) : overlap R c L hz i j ⟶
    ContactNormalizedChartZeroFamily318.scheme R c L hz i := pullback.fst _ _
instance inclusion_open (i j : Fin F.size) : IsOpenImmersion (inclusion R c L hz i j) :=
  inferInstance
@[expose] def projection (i j : Fin F.size) : overlap R c L hz i j ⟶
    ProjectiveParameterSliceSchemes318.overlap R P i j := pullback.snd _ _

/-- The actual scheme transition between the two original zero-family
open overlaps. First use the classified-section unit comparison over
one base, then the specified original base-overlap isomorphism. -/
@[expose] def transition (i j : Fin F.size) : overlap R c L hz i j ≅ overlap R c L hz j i :=
  (ContactNormalizedZeroOverlap318.iso R c L hz i j).symm ≪≫
    PullbackBaseIso318.iso (p j) (inc j i) (e i j)

@[reassoc] lemma transition_projection (i j : Fin F.size) :
    (transition R c L hz i j).hom ≫ projection R c L hz j i=
      projection R c L hz i j ≫ (e i j).hom := by
  rw [transition,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  change _ ≫ (PullbackBaseIso318.hom (p j) (inc j i) (e i j) ≫ pullback.snd _ _)=_
  rw [PullbackBaseIso318.hom_snd,← Category.assoc]
  congr 1
  rw [← ContactNormalizedZeroOverlap318.iso_projection R c L hz i j,
    Iso.inv_hom_id_assoc]

/-- The zero-family overlap transition covers the SAME original
normalized parameter transition and respects both chart projections. -/
@[reassoc] lemma transition_chart_projection (i j : Fin F.size) :
    (transition R c L hz i j).hom ≫ inclusion R c L hz j i ≫ p j=
      projection R c L hz i j ≫ (e i j).hom ≫ inc j i := by
  change _ ≫ (pullback.fst _ _ ≫ p j)=_
  rw [pullback.condition,← Category.assoc,transition_projection,Category.assoc]
end ContactNormalizedZeroTransitions318
