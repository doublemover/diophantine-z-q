module
public import ContactNormalizedZeroProjection318
public section
noncomputable section
namespace ContactNormalizedZeroCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318

lemma gluing_square (D : Scheme.GlueData) (i j : D.J) :
    IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
  IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)

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
local notation "z" => ContactNormalizedGlobalZero318.into R c L hz
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "proj" => ContactNormalizedZeroTransitions318.projection R c L hz
local notation "t" => ContactNormalizedZeroTransitions318.transition R c L hz
local notation "π" => ContactNormalizedZeroProjection318.projection R c L hz

/-- Actual opposite chart comparison is Cartesian over the actual
opposite-base overlap map, by its original same-base pullback iso. -/
lemma overlap_square (i j : Fin F.size) : IsPullback ((t i j).hom ≫ inc j i) (proj i j)
    (p j) (ContactNormalizedZeroOverlap318.right R c L hz i j) := by
  apply IsPullback.of_iso_pullback
    (i := (ContactNormalizedZeroOverlap318.iso R c L hz i j).symm)
  · constructor
    simpa only [Category.assoc,ContactNormalizedZeroOverlap318.right] using
      ContactNormalizedZeroTransitions318.transition_chart_projection R c L hz i j
  · rw [ContactNormalizedZeroTransitions318.transition,Iso.trans_hom,Iso.symm_hom,
      Category.assoc,ContactNormalizedZeroTransitions318.inclusion,PullbackBaseIso318.hom_fst]
    rfl
  · change (ContactNormalizedZeroOverlap318.iso R c L hz i j).inv ≫
      pullback.snd _ _=_
    rw [← ContactNormalizedZeroOverlap318.iso_projection R c L hz i j,Iso.inv_hom_id_assoc]

/-- Every ORIGINAL finite-flat chart family is the genuine base change
of the global zero projection along its normalized parameter open.
This is a full scheme Cartesian square, not inferred from chart points. -/
lemma square (i : Fin F.size) : IsPullback (z i) (p i) π (u i) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (ContactNormalizedGlobalZero318.cover R c L hz)
  intro j
  have hZ := gluing_square (ContactNormalizedGlobalZero318.data R c L hz) i j
  have hb := (gluing_square (ProjectiveParameterSliceGluing318.data R P) i j).flip
  have hp := (overlap_square R c L hz i j).paste_vert hb
  change IsPullback (pullback.snd (z i) (z j)) (pullback.fst (z i) (z j) ≫ p i)
    (z j ≫ π) (u i)
  apply hp.of_iso hZ.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using hZ.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,hZ.isoPullback_hom_fst]
    exact (pullback.condition (f:=p i)
      (g:=ProjectiveParameterSliceSchemes318.inclusion R P i j)).symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    exact (ContactNormalizedZeroProjection318.into_projection R c L hz j).symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
end ContactNormalizedZeroCartesian318
