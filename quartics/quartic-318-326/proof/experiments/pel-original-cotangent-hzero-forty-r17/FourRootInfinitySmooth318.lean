module
public import FourRootInfinityReducedPresentation318
public section
noncomputable section
namespace FourRootInfinitySmooth318
open Algebra FourRootCoordinateOverlap318
open FourRootInfinityReducedPresentation318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
@[expose] def d (k:Fin 3):Infinity b:=algebraMap ℂ (Infinity b) (b 0-b k.succ)
@[expose] def parameter:Infinity b:=FourRootInfinityCoordinateRing318.coordinate b none

lemma jacobian_square:(presentation b).jacobian^2=
    64*(1+d b 0*parameter b^2)*(1+d b 1*parameter b^2)*(1+d b 2*parameter b^2):=by
  rw [jacobian_formula]
  simp only [Fin.prod_univ_succ,Fin.succ_zero_eq_one,Fin.prod_univ_zero,
    mul_one,mul_pow,FourRootInfinityCoordinateRing318.relation]
  dsimp [d,parameter]
  ring

/-- The genuine overlap and the genuine three-root Jacobian neighborhood
cover the ENTIRE original infinity ring. At u=0 all three ratios are units,
so all eight infinity points remain in the smooth chart. -/
theorem cover_span:Ideal.span ({parameter b,(presentation b).jacobian}:Set (Infinity b))=⊤:=by
  let I:=Ideal.span ({parameter b,(presentation b).jacobian}:Set (Infinity b))
  have hu:parameter b∈I:=Ideal.subset_span (by simp)
  have hj:(presentation b).jacobian∈I:=Ideal.subset_span (by simp)
  have hh:=I.sub_mem (I.mul_mem_left (presentation b).jacobian hj)
    (I.mul_mem_left (64*((d b 0+d b 1+d b 2)*parameter b+
      (d b 0*d b 1+d b 0*d b 2+d b 1*d b 2)*parameter b^3+
      (d b 0*d b 1*d b 2)*parameter b^5)) hu)
  have h64:(64:Infinity b)∈I:=by
    convert hh using 1
    rw [←pow_two,jacobian_square]
    ring
  apply I.eq_top_of_isUnit_mem h64
  simpa only [map_ofNat] using (IsUnit.mk0 (64:ℂ) (by norm_num)).map (algebraMap ℂ (Infinity b))

theorem smooth:Algebra.Smooth ℂ (Infinity b):=by
  letI:Algebra.Smooth ℂ (Affine b):=FourRootAffineSmooth318.smooth b hb
  letI hAO:Algebra.Smooth ℂ (AffineOverlap b):=Algebra.Smooth.comp ℂ (Affine b) _
  have hIO:Algebra.Smooth ℂ (InfinityOverlap b):=
    Algebra.Smooth.of_equiv (FourRootCoordinateOverlap318.overlapEquiv b).symm
  rw [←RingHom.smooth_algebraMap]
  apply RingHom.Smooth.ofLocalizationSpanTarget _
    {parameter b,(presentation b).jacobian} (cover_span b)
  rintro ⟨r,hr⟩
  rcases Set.mem_insert_iff.mp hr with rfl|hr
  · rw [←IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    exact hIO
  · have he:r=(presentation b).jacobian:=Set.mem_singleton_iff.mp hr
    subst r
    rw [←IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    letI:Algebra.IsStandardSmooth ℂ (Localization.Away (presentation b).jacobian):=
      JacobianLocalSmooth318.localization_jacobian (presentation b)
    infer_instance

/-- Normality of the whole normalized infinity chart, not merely its
punctured overlap and not a component selected at an infinity point. -/
theorem integrallyClosed:IsIntegrallyClosed (Infinity b):=by
  letI:=FourRootInfinityDomain318.infinity_domain b hb
  letI:=smooth b hb
  exact SmoothDomainNormal318.integrallyClosed ℂ (Infinity b)
end FourRootInfinitySmooth318
