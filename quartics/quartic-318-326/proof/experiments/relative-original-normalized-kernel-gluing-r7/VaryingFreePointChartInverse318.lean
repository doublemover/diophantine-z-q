module
public import VaryingNormalizedGlobalPoint318
public section
noncomputable section
namespace VaryingFreePointChartInverse318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (w : ι → List A)
  (c : VaryingNormalizedWordParameter318.ring R A ι w →ₐ[R] S)
@[expose] def ideal : VaryingFreeIdealClassifyingMap318.IdealData R A ι S :=
  VaryingNormalizedGlobalPoint318.ideal R A ι w S (VaryingNormalizedWordParameter318.toPoint R A ι w S c)
lemma classify_ideal : VaryingFreeIdealClassifyingMap318.classify R A ι S (ideal R A ι S w c)=
    Spec.map (CommRingCat.ofHom c.toRingHom) ≫ VaryingWordChartGluing318.into R A ι w := by
  have h := VaryingNormalizedGlobalPoint318.classify_ideal R A ι w S
    (VaryingNormalizedWordParameter318.toPoint R A ι w S c)
  have hc : (VaryingNormalizedWordParameter318.points R A ι w S).symm
      (VaryingNormalizedWordParameter318.toPoint R A ι w S c)=c :=
    (VaryingNormalizedWordParameter318.points R A ι w S).symm_apply_apply c
  simpa only [hc] using h
/-- The right inverse holds on every actual normalized parameter chart,
with no extra normalization hypothesis on the original point. -/
lemma right_inverse (x : VaryingFreeParameterPoints318.FreePoint R A ι S)
    (h : x.val.val=Spec.map (CommRingCat.ofHom c.toRingHom) ≫ VaryingWordChartGluing318.into R A ι w) :
    VaryingFreeParameterPoints318.classify R A ι S (VaryingFreeParameterPoints318.recover R A ι S x)=x := by
  have hx : VaryingFreeParameterPoints318.classify R A ι S (ideal R A ι S w c)=x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (classify_ideal R A ι S w c).trans h.symm
  rw [← hx,VaryingFreeParameterPoints318.recover_classify]
end VaryingFreePointChartInverse318
