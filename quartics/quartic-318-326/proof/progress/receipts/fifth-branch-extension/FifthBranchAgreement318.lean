module
public import FifthBranchOverlap318
public import FifthBranchScheme318
import all WeierstrassGluing318
public section
noncomputable section
namespace FifthBranchAgreement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassOverlap318
open FifthCharacterShortPolynomial318 FifthBranchEquation318 FifthBranchLocal318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
section Chart
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
/-- Genuine chart agreement from the two transition equations, over every
coefficient algebra. The localization lift, not geometric points, proves equality. -/
theorem chart_agreement (a b:R) (f:Affine a b→ₐ[R]S) (g:Infinity a b→ₐ[R]S)
    (hx:g (InfinityChart318.x a b)*f (ShortAffineJacobian318.y a b)=f (ShortAffineJacobian318.x a b))
    (hy:g (InfinityChart318.z a b)*f (ShortAffineJacobian318.y a b)=1) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart a b=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ WeierstrassGluing318.infinityChart a b:=by
  let k:InfinityOverlap a b→ₐ[R]S:=IsLocalization.Away.liftAlgHom (f:=g)
    (InfinityChart318.z a b) (IsUnit.of_mul_eq_one _ hy)
  have hk (r:Infinity a b):k (algebraMap (Infinity a b) (InfinityOverlap a b) r)=g r:=by
    simp [k,IsLocalization.Away.liftAlgHom_apply]
  have hii:k (ii a b)=f (ShortAffineJacobian318.y a b):=by
    have hz:=congrArg k (iz_ii a b)
    simp only [map_mul,map_one] at hz
    rw [show k (iz a b)=g (InfinityChart318.z a b) from hk _] at hz
    calc
      _=k (ii a b)*(g (InfinityChart318.z a b)*f (ShortAffineJacobian318.y a b)):=by rw [hy,mul_one]
      _=(g (InfinityChart318.z a b)*k (ii a b))*f (ShortAffineJacobian318.y a b):=by ring
      _=f (ShortAffineJacobian318.y a b):=by rw [hz,one_mul]
  have hf:k.comp (toInfinityBase a b)=f:=by
    apply affine_hom_ext
    · simp only [AlgHom.comp_apply,toInfinityBase_x,map_mul]
      rw [show k (ix a b)=g (InfinityChart318.x a b) from hk _,hii,hx]
    · simp only [AlgHom.comp_apply,toInfinityBase_y,hii]
  have hfinite:Spec.map (CommRingCat.ofHom k.toRingHom) ≫ WeierstrassGluing318.intoAffine a b=
      Spec.map (CommRingCat.ofHom f.toRingHom):=by
    rw [WeierstrassGluing318.intoAffine_eq,←Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (k.comp (toInfinityBase a b)).toRingHom)=_
    rw [hf]
  have hinfty:Spec.map (CommRingCat.ofHom k.toRingHom) ≫ WeierstrassGluing318.intoInfinity a b=
      Spec.map (CommRingCat.ofHom g.toRingHom):=by
    unfold WeierstrassGluing318.intoInfinity
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact hk
  rw [←hfinite,←hinfty,Category.assoc,Category.assoc]
  exact congrArg (fun z=>Spec.map (CommRingCat.ofHom k.toRingHom) ≫ z)
    (pushout.condition (f:=WeierstrassGluing318.intoAffine a b) (g:=WeierstrassGluing318.intoInfinity a b))
end Chart

section Branch
variable {S:Type} [CommRing S] [Algebra ℚ S]
/-- Exact overlap with the reciprocal short coordinates, stated by crossed
coordinate equations so it applies to either order of the two localizations. -/
theorem agreement (f:Local→ₐ[ℚ]S) (g:ShortAffineJacobian318.Ring A B→ₐ[ℚ]S)
    (ht:IsUnit (f t))
    (hx:g (ShortAffineJacobian318.x A B)*f t=algebraMap ℚ S (xScale:ℚ)+algebraMap ℚ S shift*f t)
    (hy:g (ShortAffineJacobian318.y A B)*(f t)^2=algebraMap ℚ S (yScale:ℚ)*f w) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ WeierstrassGluing318.finiteChart A B=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ FifthBranchScheme318.intoCompleted:=by
  let nn:Sˣ:=Units.map f.toMonoidHom nUnit
  let hh:Sˣ:=Units.map f.toMonoidHom hUnit
  let tt:Sˣ:=ht.unit
  have hn0:(nn:S)=f (nUnit:Local):=by simp [nn]
  have hh0:(hh:S)=f (hUnit:Local):=by simp [hh]
  have hn:(nn:S)=algebraMap ℚ S (yScale:ℚ):=(congrArg f nUnit_value).trans (f.commutes _)
  have ht':(tt:S)=f t:=ht.unit_spec
  have hw:(f w)^2=(tt:S)*(hh:S):=by
    simpa only [map_pow,map_mul,ht',hh0] using congrArg f curve_equation
  have hu:f U*↑(nn*hh)=(algebraMap ℚ S (xScale:ℚ)+algebraMap ℚ S shift*(tt:S))*f w:=by
    have h:=congrArg f (outU_den (algebraMap ℚ Local (xScale:ℚ)) (algebraMap ℚ Local shift) t w nUnit hUnit)
    simpa only [map_mul,map_add,f.commutes,ht',U,Units.val_mul,hn0,hh0] using h
  have hv:f V*↑(nn*hh)=(tt:S)*f w:=by
    have h:=congrArg f (outV_den t w nUnit hUnit)
    simpa only [map_mul,ht',V,Units.val_mul,hn0,hh0] using h
  have hx':g (ShortAffineJacobian318.x A B)*(tt:S)=algebraMap ℚ S (xScale:ℚ)+algebraMap ℚ S shift*(tt:S):=by simpa only [ht'] using hx
  have hy':g (ShortAffineJacobian318.y A B)*(tt:S)^2=(nn:S)*f w:=by simpa only [ht',hn] using hy
  rw [FifthBranchScheme318.intoCompleted,←Category.assoc,←Spec.map_comp]
  apply chart_agreement A B g (f.comp infinityMap)
  · simp only [AlgHom.comp_apply,infinityMap_x]
    change f U*g (ShortAffineJacobian318.y A B)=g (ShortAffineJacobian318.x A B)
    exact FifthBranchOverlap318.output_x _ _ _ _ _ _ nn hh tt hw hu hx' hy'
  · simp only [AlgHom.comp_apply,infinityMap_z]
    change f V*g (ShortAffineJacobian318.y A B)=1
    exact FifthBranchOverlap318.output_y _ _ _ nn hh tt hw hv hy'
end Branch
end FifthBranchAgreement318
