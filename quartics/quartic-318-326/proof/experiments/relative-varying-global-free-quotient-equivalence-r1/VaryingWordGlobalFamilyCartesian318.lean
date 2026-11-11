module
public import VaryingWordGlobalFamilyProjection318
public section
noncomputable section
namespace VaryingWordGlobalFamilyCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "p" => VaryingNormalizedUniversalFamily318.projection R A ι
local notation "u" => VaryingWordChartGluing318.into R A ι
local notation "z" => VaryingWordFamilyGluing318.into R A ι
local notation "inc" => VaryingWordOverlapFamily318.into R A ι
local notation "proj" => VaryingWordOverlapFamily318.projection R A ι
local notation "t" => VaryingWordFamilyTransition318.transition R A ι
local notation "baseinc" => VaryingNormalizedOverlapScheme318.into R A ι
local notation "baset" => VaryingNormalizedOverlapScheme318.transition R A ι
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι

private lemma gluing_square (D : Scheme.GlueData.{u}) (i j : D.J) :
    IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
  IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)

/-- The opposite family restriction is Cartesian over the actual opposite
base restriction, using both regular transition isomorphisms. -/
lemma opposite_square (w v : ι → List A) :
    IsPullback ((t w v).hom ≫ inc v w) (proj w v) (p v) (baset w v ≫ baseinc v w) := by
  apply (VaryingWordOverlapFamily318.cartesian R A ι v w).of_iso'
    (t w v) (Iso.refl _) (VaryingWordOverlapIso318.overlapIso R A ι w v) (Iso.refl _)
  · simp only [Iso.refl_hom,Category.comp_id]
  · exact VaryingWordFamilyTransition318.transition_projection R A ι w v
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id]

/-- Each ORIGINAL quotient chart family is the actual scheme base change
of the global family over its parameter chart. No pointwise inference. -/
lemma square (w : ι → List A) : IsPullback (z w) (p w) π (u w) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (VaryingWordFamilyGluing318.cover R A ι)
  intro v
  have hZ := gluing_square (VaryingWordFamilyGluing318.data R A ι) w v
  have hb := (gluing_square (VaryingWordChartGluing318.data R A ι) w v).flip
  have hp := (opposite_square R A ι w v).paste_vert hb
  change IsPullback (pullback.snd (z w) (z v)) (pullback.fst (z w) (z v) ≫ p w)
    (z v ≫ π) (u w)
  apply hp.of_iso hZ.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using hZ.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,hZ.isoPullback_hom_fst]
    exact (VaryingWordOverlapFamily318.cartesian R A ι w v).w.symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    exact (VaryingWordGlobalFamilyProjection318.into_projection R A ι v).symm
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
end VaryingWordGlobalFamilyCartesian318
