module
public import ContactUnitZeroOriginal318
public import ContactZeroTripleTransition318
public section
noncomputable section
namespace ContactZeroOverlapOriginal318
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
local notation "chart" => ContactNormalizedOriginalCurve318.chart R c L hz
local notation "left" => ContactNormalizedZeroOverlap318.left R c L hz
local notation "right" => ContactNormalizedZeroOverlap318.right R c L hz
variable (i j : Fin F.size)

/-- The original same-base overlap comparison preserves the full old
curve map through the original normalized chart, not just its base. -/
@[reassoc] lemma same_base : (ContactNormalizedZeroOverlap318.iso R c L hz i j).hom ≫
    pullback.fst (p i) (left i j) ≫ chart i=
      pullback.fst (p j) (right i j) ≫ chart j := by
  simp only [ContactNormalizedZeroOverlap318.iso,ContactNormalizedOriginalCurve318.chart,
    Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [RestrictedFamilyOriginal.two_inv_assoc]
  rw [ContactNormalizedOverlapCoefficients318.zeroIso,
    ContactUnitZeroOriginal318.original,RestrictedFamilyOriginal.two_assoc]


/-- The ACTUAL opposite-overlap transition preserves the SAME original
curve map after changing to the actual opposite coefficient ring. -/
@[reassoc] lemma transition :
    (ContactNormalizedZeroTransitions318.transition R c L hz i j).hom ≫
      ContactNormalizedZeroTransitions318.inclusion R c L hz j i ≫ chart j=
    ContactNormalizedZeroTransitions318.inclusion R c L hz i j ≫ chart i := by
  rw [ContactNormalizedZeroTransitions318.transition,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,ContactNormalizedZeroTransitions318.inclusion,
    PullbackBaseIso318.hom_fst_assoc]
  rw [← same_base R c L hz i j,Iso.inv_hom_id_assoc]
end ContactZeroOverlapOriginal318
