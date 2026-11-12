module
public import PELOriginalWholeNativeNegation318
public import NormalizedLegendreWholeProjection318
public section
noncomputable section
namespace NormalizedLegendreNativeNegation318
open AlgebraicGeometry CategoryTheory
open NormalizedLegendreProjectiveModel318 NormalizedLegendreFieldPoints318
open NormalizedLegendreWholeProjection318

lemma translated_sign_ring (l:ℂ) (p:FinitePoints l):
    (AffineEquationFunctor318.toHom (A l) (B l) (translated l p)).comp
      (ChartNegation318.affineNeg (A l) (B l))=
    AffineEquationFunctor318.toHom (A l) (B l) (translated l (sign l p)):=by
  apply WeierstrassOverlap318.affine_hom_ext
  · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_x,
      AffineEquationFunctor318.toHom_x]
    rfl
  · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg,
      AffineEquationFunctor318.toHom_y]
    rfl

/-- Native whole-scheme negation acts as the literal ordinate sign on
ALL completed complex points, with the independently constructed point
bijection and its true infinity section unchanged. -/
theorem native_point_action (l:ℂ) (p:Option (FinitePoints l)):
    (schemeEquiv l p).val≫GluedNegation318.negation (A l) (B l)=
    (schemeEquiv l (deck l p)).val:=by
  cases p with
  | none=>
    change (Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))≫
      WeierstrassGluing318.infinity (A l) (B l))≫GluedNegation318.negation (A l) (B l)=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))≫WeierstrassGluing318.infinity (A l) (B l)
    rw [Category.assoc,GluedNegation318.infinity_fixed]
  | some p=>
    change (Spec.map (CommRingCat.ofHom
      (AffineEquationFunctor318.toHom (A l) (B l) (translated l p)).toRingHom)≫
      WeierstrassGluing318.finiteChart (A l) (B l))≫GluedNegation318.negation (A l) (B l)=
      Spec.map (CommRingCat.ofHom
        (AffineEquationFunctor318.toHom (A l) (B l) (translated l (sign l p))).toRingHom)≫
      WeierstrassGluing318.finiteChart (A l) (B l)
    rw [Category.assoc,GluedNegation318.finiteChart_negation,←Category.assoc]
    unfold GluedNegation318.finiteNeg
    rw [←Spec.map_comp]
    exact congrArg (fun f=>Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f))≫
      WeierstrassGluing318.finiteChart (A l) (B l)) (translated_sign_ring l p)
end NormalizedLegendreNativeNegation318
