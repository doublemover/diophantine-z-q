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

@[expose] def finiteHom : ℚ[X] →+* Ring := Polynomial.toLaurent

@[expose] def infinityHom : ℚ[X] →+* Ring :=
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
  · change equiv (Polynomial.aeval ProjectiveLineOverlap318.s X) = infinityHom X
    rw [Polynomial.aeval_X,infinityHom_X]
    exact equiv_s

@[expose] def finiteInclusion : Spec (CommRingCat.of Ring) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom finiteHom)

@[expose] def infinityInclusion : Spec (CommRingCat.of Ring) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom infinityHom)

/-- Normalize the Spec composition on abstract rings before specializing
large original localization algebras. -/
private lemma spec_comp {A B C : CommRingCat.{0}} (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]
  rfl

private lemma spec_iso_hom {A B : CommRingCat.{0}} (e : A ≃+* B) :
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

lemma finite_square : schemeIso.hom ≫ ProjectiveLineOverlap318.finiteInclusion =
    finiteInclusion := by
  have h : equiv.toRingHom.comp (algebraMap ℚ[X] ProjectiveLineOverlap318.A) = finiteHom := by
    apply RingHom.ext
    intro p
    exact equiv.commutes p
  have hi : schemeIso.hom = Spec.map (CommRingCat.ofHom equiv.toRingHom) :=
    spec_iso_hom (A := CommRingCat.of ProjectiveLineOverlap318.A) (B := CommRingCat.of Ring)
      equiv.toRingEquiv
  exact (congrArg (fun q => q ≫ ProjectiveLineOverlap318.finiteInclusion) hi).trans
    ((spec_comp (A := CommRingCat.of ℚ[X]) (B := CommRingCat.of ProjectiveLineOverlap318.A)
      (C := CommRingCat.of Ring) (algebraMap ℚ[X] ProjectiveLineOverlap318.A) equiv.toRingHom).trans
      (congrArg (fun q : ℚ[X] →+* Ring => Spec.map (CommRingCat.ofHom q)) h))

lemma infinity_square : schemeIso.hom ≫ ProjectiveLineOverlap318.infinityInclusion =
    infinityInclusion := by
  have hi : schemeIso.hom = Spec.map (CommRingCat.ofHom equiv.toRingHom) :=
    spec_iso_hom (A := CommRingCat.of ProjectiveLineOverlap318.A) (B := CommRingCat.of Ring)
      equiv.toRingEquiv
  exact (congrArg (fun q => q ≫ ProjectiveLineOverlap318.infinityInclusion) hi).trans
    ((spec_comp (A := CommRingCat.of ℚ[X]) (B := CommRingCat.of ProjectiveLineOverlap318.A)
      (C := CommRingCat.of Ring) (Polynomial.aeval ProjectiveLineOverlap318.s).toRingHom equiv.toRingHom).trans
      (congrArg (fun q : ℚ[X] →+* Ring => Spec.map (CommRingCat.ofHom q)) infinity_ring_square))

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

@[expose] def embedding : Spec (CommRingCat.of Ring) ⟶ ProjectiveJLine318.scheme ℚ :=
  finiteInclusion ≫ JLineAtlas318.chart ℚ 1

/-- Named public equation for the original opaque embedding. Downstream
modules rewrite this theorem, not the unexposed definition body. -/
lemma embedding_eq : embedding=finiteInclusion ≫ JLineAtlas318.chart ℚ 1 := rfl
instance embedding_open : IsOpenImmersion embedding := by unfold embedding; infer_instance

lemma embedding_square : schemeIso.hom ≫ ProjectiveLineOverlap318.embedding = embedding := by
  unfold ProjectiveLineOverlap318.embedding embedding
  rw [← Category.assoc,finite_square]

/-- Morphism equality transports its open range without abstracting a
morphism while retaining an instance dependent on the old morphism. -/
private lemma opensRange_congr {X Y : Scheme.{0}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f=g) : f.opensRange=g.opensRange := by
  subst g
  rfl

lemma full_intersection : (JLineAtlas318.chart ℚ 1).opensRange ⊓
    (JLineAtlas318.chart ℚ 0).opensRange = embedding.opensRange := by
  calc
    _ = ProjectiveLineOverlap318.embedding.opensRange := ProjectiveLineOverlap318.full_intersection
    _ = (schemeIso.hom ≫ ProjectiveLineOverlap318.embedding).opensRange :=
      (Scheme.Hom.opensRange_comp_of_isIso _ _).symm
    _ = embedding.opensRange := opensRange_congr embedding_square

lemma finite_range : finiteInclusion.opensRange = PrimeSpectrum.basicOpen (X : ℚ[X]) := by
  calc
    _ = (schemeIso.hom ≫ ProjectiveLineOverlap318.finiteInclusion).opensRange :=
      (opensRange_congr finite_square).symm
    _ = ProjectiveLineOverlap318.finiteInclusion.opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = _ := ProjectiveLineOverlap318.finite_range

/-- Actual scheme pullback with the literal original Laurent maps. -/
lemma actual_pullback : IsPullback infinityInclusion finiteInclusion
    (JLineAtlas318.chart ℚ 0) (JLineAtlas318.chart ℚ 1) := by
  apply IsOpenImmersion.isPullback
  · exact maps_agree
  · exact (congrArg (fun U => JLineAtlas318.chart ℚ 1 ⁻¹ᵁ U)
        (Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart ℚ 0)).symm).trans
      (ProjectiveLineOverlap318.chart_one_preimage_zero.trans finite_range.symm)
end OriginalLaurentProjectiveOverlap318
