module
public import FourRootDerivativeFiniteIdeal318
public import FourRootActualInfinityKaehler318
public section
noncomputable section
namespace FourRootDerivativeInfinityIdeal318
open FourRootDerivativeZeroIdeals318 FourRootActualInfinityKaehler318
open FourRootReciprocalBranchData318
open scoped BigOperators
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
@[expose] def ratioProduct:I b:=∏i:Fin 4,FourRootInfinityCoordinateRing318.coordinate b (some i)
@[expose] def scaleProduct:ℂ:=∏j:Fin 3,scale b j
lemma scaleProduct_ne:scaleProduct b≠0:=by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact scale_ne_zero b hb j
lemma ratio_image:FourRootInfinityAffineComparison318.equivalence b hb (ratioProduct b)=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring (branches b)) (scaleProduct b)*
      FourRootDerivativeFiniteIdeal318.otherProduct (branches b) 0:=by
  simp [ratioProduct,scaleProduct,FourRootInfinityAffineComparison318.equivalence,
    FourRootInfinityAffineComparison318.ratio,FourRootDerivativeFiniteIdeal318.otherProduct,
    FourRootPivot318.indices,Fin.prod_univ_succ] <;> ring
/-- All three original infinity ratios are units on the genuine infinity
canonical neighborhood. This is derived through the SAME whole-ring
reciprocal model, including all eight u=0 centers. -/
lemma localized_ratios_unit:IsUnit
    (algebraMap (I b) (SourceRing b hb) (ratioProduct b)):=by
  let e:=localizationEquiv b hb
  have hscale:IsUnit (algebraMap ℂ
      (FourRootActualBranchKaehler318.SourceRing (branches b) 0) (scaleProduct b)):=
    (isUnit_iff_ne_zero.mpr (scaleProduct_ne b hb)).map _
  have h:IsUnit (e (algebraMap (I b) (SourceRing b hb) (ratioProduct b))):=by
    rw [show e=localizationEquiv b hb from rfl,on_source,ratio_image,map_mul,
      ←IsScalarTower.algebraMap_apply ℂ (FourRootAffineCoordinateRing318.Ring (branches b))
        (FourRootActualBranchKaehler318.SourceRing (branches b) 0)]
    exact hscale.mul (FourRootDerivativeFiniteIdeal318.localized_other_unit (branches b) 0)
  simpa only [AlgEquiv.symm_apply_apply] using h.map e.symm.toRingHom
lemma generator_factor:algebraMap (I b) (SourceRing b hb) (infinityGenerator b)=
    coordinate b hb*algebraMap (I b) (SourceRing b hb) (ratioProduct b):=by
  rw [infinityGenerator,map_mul]
  rfl
theorem localized_ideal:
    (infinityIdeal b).map (algebraMap (I b) (SourceRing b hb))=
      Ideal.span {coordinate b hb}:=by
  rw [infinityIdeal,Ideal.map_span,Set.image_singleton,generator_factor,
    Ideal.span_singleton_mul_right_unit (localized_ratios_unit b hb)]
lemma two_unit:IsUnit (2:SourceRing b hb):=by
  have h:IsUnit (2:ℂ):=isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℂ (SourceRing b hb))
/-- The global ideal restricts to the literal coefficient ideal of the
ACTUAL derivative dv=2u du, over v=u². No rank-eight u-base or meromorphic
dt coefficient is substituted. -/
theorem derivative_ideal:
    (infinityIdeal b).map (algebraMap (I b) (SourceRing b hb))=
      Ideal.span {2*coordinate b hb}:=by
  rw [localized_ideal,Ideal.span_singleton_mul_left_unit (two_unit b hb)]
end FourRootDerivativeInfinityIdeal318
