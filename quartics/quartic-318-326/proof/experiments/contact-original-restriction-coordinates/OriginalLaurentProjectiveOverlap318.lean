module
public import ProjectiveLineOverlap318
public import Mathlib.Algebra.Polynomial.Laurent

public section
noncomputable section
namespace OriginalLaurentProjectiveOverlap318
open AlgebraicGeometry CategoryTheory Polynomial LaurentPolynomial
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Ring := LaurentPolynomial ℚ

/-- Uniqueness of the original localization identifies the entire old
projective overlap with the actual Laurent ring. -/
def equiv : ProjectiveLineOverlap318.A ≃ₐ[ℚ[X]] Ring :=
  IsLocalization.algEquiv (Submonoid.powers (X : ℚ[X])) _ _

def schemeIso : Spec (CommRingCat.of Ring) ≅ Spec (CommRingCat.of ProjectiveLineOverlap318.A) :=
  Scheme.Spec.mapIso equiv.toRingEquiv.toCommRingCatIso.op

def finiteHom : ℚ[X] →+* Ring := Polynomial.toLaurent

def infinityHom : ℚ[X] →+* Ring :=
  LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent

lemma equiv_t : equiv ProjectiveLineOverlap318.t = (T 1 : Ring) := by
  change equiv (algebraMap ℚ[X] ProjectiveLineOverlap318.A X) = _
  rw [equiv.commutes]
  exact Polynomial.toLaurent_X

lemma equiv_s : equiv ProjectiveLineOverlap318.s = (T (-1) : Ring) := by
  apply mul_left_cancel₀ (LaurentPolynomial.isUnit_T (R:=ℚ) 1).ne_zero
  calc
    (T 1 : Ring) * equiv ProjectiveLineOverlap318.s =
        equiv (ProjectiveLineOverlap318.t * ProjectiveLineOverlap318.s) := by
      rw [map_mul,equiv_t]
    _ = 1 := by rw [ProjectiveLineOverlap318.ts,map_one]
    _ = T 1 * T (-1) := by rw [← LaurentPolynomial.T_add] <;> norm_num

lemma infinityHom_X : infinityHom X = (T (-1) : Ring) := by
  simp [infinityHom]

lemma infinity_ring_square : equiv.toRingHom.comp
    (Polynomial.aeval ProjectiveLineOverlap318.s).toRingHom = infinityHom := by
  apply Polynomial.ringHom_ext
  · intro q
    simp [infinityHom,RingHom.comp_apply]
  · simpa only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Polynomial.aeval_X,infinityHom_X] using equiv_s

def finiteInclusion : Spec (CommRingCat.of Ring) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom finiteHom)

def infinityInclusion : Spec (CommRingCat.of Ring) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom infinityHom)

lemma finite_square : schemeIso.hom ≫ ProjectiveLineOverlap318.finiteInclusion =
    finiteInclusion := by
  change Spec.map (CommRingCat.ofHom equiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] ProjectiveLineOverlap318.A)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact equiv.commutes p

lemma infinity_square : schemeIso.hom ≫ ProjectiveLineOverlap318.infinityInclusion =
    infinityInclusion := by
  change Spec.map (CommRingCat.ofHom equiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.aeval ProjectiveLineOverlap318.s).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom infinity_ring_square

instance finite_open : IsOpenImmersion finiteInclusion := by
  rw [← finite_square]
  infer_instance
instance infinity_open : IsOpenImmersion infinityInclusion := by
  rw [← infinity_square]
  infer_instance

lemma maps_agree : finiteInclusion ≫ JLineAtlas318.chart ℚ 1 =
    infinityInclusion ≫ JLineAtlas318.chart ℚ 0 := by
  rw [← finite_square,← infinity_square,Category.assoc,Category.assoc,
    ProjectiveLineOverlap318.maps_agree]

def embedding : Spec (CommRingCat.of Ring) ⟶ ProjectiveJLine318.scheme ℚ :=
  finiteInclusion ≫ JLineAtlas318.chart ℚ 1
instance embedding_open : IsOpenImmersion embedding := by unfold embedding; infer_instance

lemma embedding_square : schemeIso.hom ≫ ProjectiveLineOverlap318.embedding = embedding := by
  unfold ProjectiveLineOverlap318.embedding embedding
  rw [← Category.assoc,finite_square]

lemma full_intersection : (JLineAtlas318.chart ℚ 1).opensRange ⊓
    (JLineAtlas318.chart ℚ 0).opensRange = embedding.opensRange := by
  rw [ProjectiveLineOverlap318.full_intersection,← embedding_square,
    Scheme.Hom.opensRange_comp_of_isIso]

/-- Actual scheme pullback with the literal original Laurent maps. -/
lemma actual_pullback : IsPullback infinityInclusion finiteInclusion
    (JLineAtlas318.chart ℚ 0) (JLineAtlas318.chart ℚ 1) := by
  apply IsOpenImmersion.isPullback
  · exact maps_agree
  · rw [← Scheme.Hom.image_top_eq_opensRange,
      ProjectiveLineOverlap318.chart_one_preimage_zero,← finite_square,
      Scheme.Hom.opensRange_comp_of_isIso,ProjectiveLineOverlap318.finite_range]
end OriginalLaurentProjectiveOverlap318
