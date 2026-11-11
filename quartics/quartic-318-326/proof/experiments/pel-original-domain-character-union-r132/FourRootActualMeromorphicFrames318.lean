module
public import ActualLocalizationDifferentialFrame318
public import FourRootActualInfinityTraceCotangent318
public import FourRootCoordinateOverlap318
public import ReciprocalCoordinateDifferential318
public section
noncomputable section
namespace FourRootActualMeromorphicFinite318
open Polynomial FourRootActualFractionField318 FourRootActualFiniteBranchChart318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ)(hb:Function.Injective b)(i:Fin 4)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance affineFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
lemma denominator_ne:denominator b i≠0:=by
  have hn:denominatorPolynomial b i≠0:=by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Polynomial.X_sub_C_ne_zero _
  have hi:Function.Injective (algebraMap ℂ[X] (A b)):=FaithfulSMul.algebraMap_injective _ _
  exact (map_ne_zero_iff _ hi).mpr hn
abbrev F:=FractionRing (A b)
@[expose] def frame:KaehlerDifferential ℂ (F b)≃ₗ[F b]F b:=
  ActualLocalizationDifferentialFrame318.frame (A b) (denominator b i) (denominator_ne b hb i)
    (FourRootActualBranchKaehler318.sourceFrame b i)
@[expose] def t:F b:=algebraMap (A b) (F b) (FourRootAffineCoordinateRing318.coordinate b none)
@[expose] def z:F b:=algebraMap (A b) (F b) (FourRootAffineCoordinateRing318.coordinate b (some i))
/-- In the original fraction field and actual signed-root frame,
the ORIGINAL base differential has coefficient exactly 2z_i. -/
theorem dt_coefficient:frame b hb i (KaehlerDifferential.D ℂ (F b) (t b))=2*z b i:=by
  have h:=ActualLocalizationDifferentialFrame318.frame_D (A b) (denominator b i)
    (denominator_ne b hb i) (FourRootActualBranchKaehler318.sourceFrame b i)
    (FourRootActualBranchKaehler318.sourceParameter b i)
  rw [FourRootActualBranchKaehler318.parameter_coefficient,
    FourRootActualBranchKaehler318.source_coordinate_original,map_mul,map_ofNat,
    ActualLocalizationDifferentialFrame318.on_source] at h
  simpa only [FourRootActualBranchKaehler318.sourceParameter,
    ActualLocalizationDifferentialFrame318.on_source,frame,t,z] using h
end FourRootActualMeromorphicFinite318

namespace FourRootActualMeromorphicInfinity318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
@[expose] def d:I b:=FourRootActualInfinityKaehler318.denominator b hb
lemma denominator_ne:d b hb≠0:=by
  let p:InfinityPoints b:=⟨(0,fun _=>1),rfl,by intro k;simp⟩
  have hn:=FourRootActualKaehlerNeighborhoods318.infinity_neighborhood b hb p rfl
  intro h
  exact hn (by rw [show FourRootActualInfinityKaehler318.denominator b hb=0 from h];exact Ideal.zero_mem _)
lemma original_u_ne:FourRootInfinityCoordinateRing318.coordinate b none≠0:=by
  intro h
  have he:=congrArg (FourRootInfinityAffineComparison318.equivalence b hb) h
  change FourRootAffineCoordinateRing318.coordinate (FourRootReciprocalBranchData318.branches b) (some 0)=_ at he
  rw [map_zero] at he
  exact FourRootActualLocalUniformizer318.source_root_ne_zero
    (FourRootReciprocalBranchData318.branches b)
    (FourRootReciprocalBranchData318.branches_injective b hb) 0 he
abbrev F:=FractionRing (I b)
@[expose] def frame:KaehlerDifferential ℂ (F b)≃ₗ[F b]F b:=
  ActualLocalizationDifferentialFrame318.frame (I b) (d b hb) (denominator_ne b hb)
    (FourRootActualInfinityKaehler318.frame b hb)
@[expose] def u:F b:=algebraMap (I b) (F b) (FourRootInfinityCoordinateRing318.coordinate b none)
lemma u_ne:u b≠0:=(map_ne_zero_iff _ (IsFractionRing.injective (I b) (F b))).mpr (original_u_ne b hb)
lemma du_coefficient:frame b hb (KaehlerDifferential.D ℂ (F b) (u b))=1:=by
  have h:=ActualLocalizationDifferentialFrame318.frame_D (I b) (d b hb)
    (denominator_ne b hb) (FourRootActualInfinityKaehler318.frame b hb)
    (FourRootActualInfinityKaehler318.coordinate b hb)
  rw [FourRootActualInfinityKaehler318.coordinate_normalized,map_one] at h
  simpa only [FourRootActualInfinityKaehler318.coordinate,
    ActualLocalizationDifferentialFrame318.on_source,frame,u] using h

@[expose] def overlapMap:FourRootCoordinateOverlap318.InfinityOverlap b→ₐ[ℂ]F b:=
  IsLocalization.Away.liftAlgHom (f:=IsScalarTower.toAlgHom ℂ (I b) (F b))
    (FourRootInfinityCoordinateRing318.coordinate b none) (IsUnit.mk0 _ (u_ne b hb))
lemma overlap_u:overlapMap b hb (FourRootCoordinateOverlap318.u b)=u b:=
  IsLocalization.Away.liftAlgHom_apply ..
lemma overlap_inverse:overlapMap b hb (FourRootCoordinateOverlap318.ui b)=(u b)⁻¹:=by
  have h:=congrArg (overlapMap b hb) (FourRootCoordinateOverlap318.u_ui b)
  rw [map_mul,map_one,overlap_u] at h
  apply mul_left_cancel₀ (u_ne b hb)
  exact h.trans (mul_inv_cancel₀ (u_ne b hb)).symm
/-- The original finite coordinate ring maps into the SAME infinity
fraction field by the independently proved ACTUAL overlap equations. -/
@[expose] def originalFiniteMap:FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]F b:=
  (overlapMap b hb).comp (FourRootCoordinateOverlap318.toInfinityBase b)
@[expose] def t:F b:=originalFiniteMap b hb (FourRootAffineCoordinateRing318.coordinate b none)
lemma original_coordinate:t b hb=algebraMap ℂ (F b) (b 0)+(u b)⁻¹^2:=by
  rw [t,originalFiniteMap,AlgHom.comp_apply,FourRootCoordinateOverlap318.toInfinityBase_t,
    map_add,AlgHom.commutes,map_pow,overlap_inverse]

/-- The original t-differential, not the reciprocal v-differential,
has the exact meromorphic coefficient -2/u³ in the normalized u frame. -/
theorem dt_coefficient:frame b hb (KaehlerDifferential.D ℂ (F b) (t b hb))=-(2:F b)*(u b)⁻¹^3:=by
  let t0:F b:=t b hb-algebraMap ℂ (F b) (b 0)
  have he:t0=(u b)⁻¹^2:=by rw [t0,original_coordinate,add_sub_cancel_left]
  have hs:(u b)^2*t0=algebraMap ℂ (F b) 1:=by
    rw [he,map_one,←mul_pow,mul_inv_cancel₀ (u_ne b hb),one_pow]
  have hd:=ReciprocalCoordinateDifferential318.D_of_inverse (R:=ℂ) t0 (u b) (u b)⁻¹ 1
    (mul_inv_cancel₀ (u_ne b hb)) hs
  have hc:=congrArg (frame b hb) hd
  simp only [t0,map_sub,Derivation.map_algebraMap,sub_zero,map_smul,smul_eq_mul,
    du_coefficient,mul_one] at hc
  rw [show t b hb-algebraMap ℂ (F b) (b 0)=(u b)⁻¹^2 from he] at hc
  convert hc using 1 <;> ring
lemma pole_cleared:(u b)^3*frame b hb (KaehlerDifferential.D ℂ (F b) (t b hb))=-(2:F b):=by
  rw [dt_coefficient]
  field_simp [u_ne b hb]
end FourRootActualMeromorphicInfinity318
