module
public import ContactNormalizedTripleFamilies318
public import PullbackOverlapIntersection318
public section
noncomputable section
namespace ContactNormalizedZeroIntersection318
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
local notation "p" q => ContactNormalizedChartZeroFamily318.projection R c L hz q
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "zinc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
variable (i j k : Fin F.size)
local notation "e" => ProjectiveParameterSliceTriplePullback318.comparison R P i j k
local notation "q" => ProjectiveParameterSliceTriplePullback318.first R P i j k
local notation "g" => q ≫ inc i j

lemma base_factor : e.hom ≫ (pullback.fst (inc i j) (inc i k) ≫ inc i j)=g := by
  rw [← Category.assoc,ProjectiveParameterSliceTriplePullback318.comparison_fst]

/-- The actual intersection of two ORIGINAL zero-family overlaps is
identified with the original zero chart pulled back to the LITERAL
iterated-localization triple scheme, not an abstract triple-point set. -/
@[expose] def iso : pullback (zinc i j) (zinc i k) ≅ pullback (p i) g :=
  PullbackOverlapIntersection318.iso (p i) (inc i j) (inc i k) ≪≫
  (PullbackBaseIso318.iso (p i) (pullback.fst (inc i j) (inc i k) ≫ inc i j) e).symm ≪≫
  pullback.congrHom rfl (base_factor R c L hz i j k)

/-- The comparison retains the SAME original zero-chart inclusion. -/
@[reassoc] lemma iso_original : (iso R c L hz i j k).hom ≫ pullback.fst (p i) g=
    pullback.fst (zinc i j) (zinc i k) ≫ zinc i j := by
  rw [iso,Iso.trans_hom,Iso.trans_hom,Iso.symm_hom,Category.assoc,Category.assoc,
    pullback.congrHom_hom,pullback.lift_fst,PullbackBaseIso318.inv_fst,
    PullbackOverlapIntersection318.hom_original]
end ContactNormalizedZeroIntersection318
