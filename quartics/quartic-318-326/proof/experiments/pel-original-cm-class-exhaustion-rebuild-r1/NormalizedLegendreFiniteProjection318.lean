module
public import NormalizedLegendreFieldPoints318
public import NormalizedLegendreSchemeProjection318
public import ProjectiveLineComplexSchemePoints318
public section
noncomputable section
namespace NormalizedLegendreFiniteProjection318
open AlgebraicGeometry CategoryTheory Polynomial
open NormalizedLegendreProjectiveModel318 NormalizedLegendreFieldPoints318
open ProjectiveLineComplexSchemePoints318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The map on ALL actual complex Scheme-valued points is induced by
composition with the previously constructed full Scheme projection. -/
@[expose] def project (l:ℂ)
    (p:CompletedFieldPoints318.SchemePoints (K:=ℂ) (A l) (B l)) : SchemePoints:=
  ⟨p.val ≫ NormalizedLegendreSchemeProjection318.projection l,by
    rw [Category.assoc,NormalizedLegendreSchemeProjection318.over_base]
    exact p.property⟩

/-- The concrete coordinate functor and actual full Scheme projection
commute: original Legendre t, not translated short-Weierstrass x. -/
theorem finite_projection (l:ℂ) (p:FinitePoints l) :
    project l (schemeEquiv l (some p))=chartPoint 1 p.val.1 := by
  apply Subtype.ext
  change ((finiteScheme l p).val ≫ WeierstrassGluing318.finiteChart (A l) (B l)) ≫
    NormalizedLegendreSchemeProjection318.projection l=(chartPoint 1 p.val.1).val
  rw [Category.assoc,NormalizedLegendreSchemeProjection318.finite_chart]
  change Spec.map (CommRingCat.ofHom
      (AffineEquationFunctor318.toHom (A l) (B l) (translated l p)).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℂ)
      (ShortAffineJacobian318.x (A l) (B l)+algebraMap ℂ _ (shift l))).toRingHom) ≫
      JLineAtlas318.chart ℂ 1)=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval p.val.1).toRingHom) ≫
      JLineAtlas318.chart ℂ 1
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,map_add,AlgHom.commutes,
      AffineEquationFunctor318.toHom_x]
    change p.val.1-shift l+shift l=p.val.1
    exact sub_add_cancel _ _

/-- Full finite point fibers of the actual Scheme projection are the
literal sign orbits. No quotient identification is inferred from two
unrelated points counts. -/
theorem finite_same_projection (l:ℂ) (p q:FinitePoints l) :
    project l (schemeEquiv l (some p))=project l (schemeEquiv l (some q)) ↔
      p=q ∨ sign l p=q := by
  rw [finite_projection,finite_projection]
  exact (chartPoint_injective 1).eq_iff.trans (same_coordinate l p q)

/-- Distinguishes the unique finite branch points on the SAME target.
This does not manufacture a lift from the original analytic cover. -/
theorem finite_sign_fixed (l:ℂ) (p:FinitePoints l) :
    sign l p=p ↔
      project l (schemeEquiv l (some p))=chartPoint 1 0 ∨
      project l (schemeEquiv l (some p))=chartPoint 1 1 ∨
      project l (schemeEquiv l (some p))=chartPoint 1 l := by
  simp only [sign_fixed_iff,zero_iff_branch,finite_projection,
    (chartPoint_injective 1).eq_iff]
end NormalizedLegendreFiniteProjection318
