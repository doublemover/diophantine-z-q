module
public import WeierstrassReciprocalCoordinate318
public import WeierstrassGluing318
public import JLineOverlap318
import all WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassReciprocalOverlap318
open AlgebraicGeometry CategoryTheory Polynomial
open WeierstrassReciprocalCoordinate318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] (A B:R)

@[expose] def nearBase:Spec (CommRingCat.of (Near A B))⟶InfinitySmooth318.scheme A B:=
  Spec.map (CommRingCat.ofHom (algebraMap (I A B) (Near A B)))
instance nearBase_open:IsOpenImmersion (nearBase A B):=
  IsOpenImmersion.of_isLocalization (denominator A B)
@[expose] def nearInclusion:Spec (CommRingCat.of (Common A B))⟶Spec (CommRingCat.of (Near A B)):=
  Spec.map (CommRingCat.ofHom (algebraMap (Near A B) (Common A B)))
instance nearInclusion_open:IsOpenImmersion (nearInclusion A B):=
  IsOpenImmersion.of_isLocalization (z A B)

@[expose] def toOverlap:WeierstrassOverlap318.InfinityOverlap A B→ₐ[R]Common A B:=
  IsLocalization.Away.liftAlgHom
    (f:=IsScalarTower.toAlgHom R (I A B) (Common A B)) (InfinityChart318.z A B) (by
      change IsUnit (algebraMap (I A B) (Common A B) (InfinityChart318.z A B))
      rw [IsScalarTower.algebraMap_apply (I A B) (Near A B) (Common A B)]
      exact IsLocalization.Away.algebraMap_isUnit (z A B))

lemma toOverlap_on_base (a:I A B):
    toOverlap A B (algebraMap (I A B) (WeierstrassOverlap318.InfinityOverlap A B) a)=
      algebraMap (Near A B) (Common A B) (algebraMap (I A B) (Near A B) a):=by
  simp only [toOverlap,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,
    ]
  exact IsScalarTower.algebraMap_apply (I A B) (Near A B) (Common A B) a

@[expose] def overlapInclusion:Spec (CommRingCat.of (Common A B))⟶WeierstrassGluing318.overlap A B:=
  Spec.map (CommRingCat.ofHom (toOverlap A B).toRingHom)

theorem base_square:nearInclusion A B≫nearBase A B=
    overlapInclusion A B≫WeierstrassGluing318.intoInfinity A B:=by
  unfold nearInclusion nearBase overlapInclusion WeierstrassGluing318.intoInfinity
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (toOverlap_on_base A B a).symm

theorem actual_pullback:IsPullback (overlapInclusion A B) (nearInclusion A B)
    (WeierstrassGluing318.intoInfinity A B) (nearBase A B):=by
  apply IsOpenImmersion.isPullback
  · exact base_square A B
  · have hz:(WeierstrassGluing318.intoInfinity A B).opensRange=
        PrimeSpectrum.basicOpen (InfinityChart318.z A B):=by
      apply TopologicalSpace.Opens.ext
      exact PrimeSpectrum.localization_away_comap_range _ _
    rw [hz]
    change PrimeSpectrum.basicOpen (z A B)=(nearInclusion A B).opensRange
    apply TopologicalSpace.Opens.ext
    exact (PrimeSpectrum.localization_away_comap_range _ _).symm

lemma toOverlap_ix:
    toOverlap A B (WeierstrassOverlap318.ix A B)=algebraMap (Near A B) (Common A B) (x A B):=
  toOverlap_on_base A B _
lemma toOverlap_ii:
    toOverlap A B (WeierstrassOverlap318.ii A B)=IsLocalization.Away.invSelf (z A B):=by
  have h:=congrArg (toOverlap A B) (WeierstrassOverlap318.iz_ii A B)
  simp only [map_mul,map_one] at h
  rw [show toOverlap A B (WeierstrassOverlap318.iz A B)=algebraMap (Near A B) (Common A B) (z A B)
    from toOverlap_on_base A B _] at h
  have hz:=IsLocalization.Away.mul_invSelf (S:=Common A B) (z A B)
  calc
    _=(algebraMap (Near A B) (Common A B) (z A B)*IsLocalization.Away.invSelf (z A B))*
      toOverlap A B (WeierstrassOverlap318.ii A B):=by rw [hz,one_mul]
    _=IsLocalization.Away.invSelf (z A B)*
      (algebraMap (Near A B) (Common A B) (z A B)*toOverlap A B (WeierstrassOverlap318.ii A B)):=by ring
    _=IsLocalization.Away.invSelf (z A B):=by rw [h,mul_one]

@[expose] def overlapProjection:WeierstrassGluing318.overlap A B⟶ProjectiveJLine318.scheme R:=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
    (WeierstrassOverlap318.ix A B*WeierstrassOverlap318.ii A B)).toRingHom)≫JLineAtlas318.chart R 1
@[expose] def nearProjection:Spec (CommRingCat.of (Near A B))⟶ProjectiveJLine318.scheme R:=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) (reciprocal A B)).toRingHom)≫JLineAtlas318.chart R 0

/-- Actual projective-line chart compatibility on the whole actual common
localization, induced by the unit pair from the checked coordinate identity. -/
theorem projection_compatibility:overlapInclusion A B≫overlapProjection A B=
    nearInclusion A B≫nearProjection A B:=by
  have he1:(toOverlap A B).toRingHom.comp
      (Polynomial.aeval (R:=R) (WeierstrassOverlap318.ix A B*WeierstrassOverlap318.ii A B)).toRingHom=
    (Polynomial.aeval (R:=R) (forward A B)).toRingHom:=by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,
        map_mul,toOverlap_ix,toOverlap_ii,forward]
  have he2:(algebraMap (Near A B) (Common A B)).comp (Polynomial.aeval (R:=R) (reciprocal A B)).toRingHom=
      (Polynomial.aeval (R:=R) (inverse A B)).toRingHom:=by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,
        ←IsScalarTower.algebraMap_apply R (Near A B) (Common A B)]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,inverse]
  unfold overlapInclusion overlapProjection nearInclusion nearProjection
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((toOverlap A B).toRingHom.comp
      (Polynomial.aeval (R:=R) (WeierstrassOverlap318.ix A B*WeierstrassOverlap318.ii A B)).toRingHom))≫_=
    Spec.map (CommRingCat.ofHom ((algebraMap (Near A B) (Common A B)).comp
      (Polynomial.aeval (R:=R) (reciprocal A B)).toRingHom))≫_
  rw [he1,he2]
  let q:(Common A B)ˣ:=⟨forward A B,inverse A B,forward_inverse A B,by rw [mul_comm,forward_inverse]⟩
  exact JLineOverlap318.unit_chart_overlap (R:=R) q
end WeierstrassReciprocalOverlap318
