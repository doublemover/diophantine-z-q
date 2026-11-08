module
public import WeierstrassOverlap318
public import InfinityFiniteCompatibility318
public section
noncomputable section
namespace InfinityExtraction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
@[expose] def overlap (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) :
    WeierstrassOverlap318.InfinityOverlap A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=φ) (InfinityChart318.z A B) hv
@[simp] theorem overlap_base (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) (r:InfinityChart318.Ring A B) :
    overlap A B φ hv (algebraMap (InfinityChart318.Ring A B) (WeierstrassOverlap318.InfinityOverlap A B) r)=φ r := by
  simp only [overlap,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl
@[expose] def finiteMap (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) : ShortAffineJacobian318.Ring A B →ₐ[R] S :=
  (overlap A B φ hv).comp (WeierstrassOverlap318.toInfinityBase A B)
theorem y_relation (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) :
    φ (InfinityChart318.z A B)*finiteMap A B φ hv (ShortAffineJacobian318.y A B)=1 := by
  have hh:=congrArg (overlap A B φ hv) (WeierstrassOverlap318.iz_ii A B)
  simpa only [map_mul,map_one,WeierstrassOverlap318.iz,overlap_base,
    finiteMap,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y] using hh

theorem x_relation (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) :
    φ (InfinityChart318.x A B)*finiteMap A B φ hv (ShortAffineJacobian318.y A B)=
      finiteMap A B φ hv (ShortAffineJacobian318.x A B) := by
  simp only [finiteMap,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y,
    WeierstrassOverlap318.toInfinityBase_x,map_mul,WeierstrassOverlap318.ix,overlap_base]

theorem natural (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) (g:S →ₐ[R] T) :
    g.comp (finiteMap A B φ hv)=finiteMap A B (g.comp φ) (hv.map g) := by
  have he:g.comp (overlap A B φ hv)=overlap A B (g.comp φ) (hv.map g) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (InfinityChart318.z A B))
    apply AlgHom.ext
    intro r
    change g (overlap A B φ hv (algebraMap (InfinityChart318.Ring A B)
      (WeierstrassOverlap318.InfinityOverlap A B) r))=
      overlap A B (g.comp φ) (hv.map g) (algebraMap (InfinityChart318.Ring A B)
        (WeierstrassOverlap318.InfinityOverlap A B) r)
    simp only [overlap_base,AlgHom.comp_apply]
  change (g.comp (overlap A B φ hv)).comp (WeierstrassOverlap318.toInfinityBase A B)=_
  rw [he]
  rfl

theorem input_agreement (A B:R) (φ:InfinityChart318.Ring A B →ₐ[R] S)
    (hv:IsUnit (φ (InfinityChart318.z A B))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.map (CommRingCat.ofHom (finiteMap A B φ hv).toRingHom) ≫ WeierstrassGluing318.finiteChart A B :=
  InfinityFiniteCompatibility318.scheme_agreement A B φ (finiteMap A B φ hv)
    (x_relation A B φ hv) (y_relation A B φ hv)
end InfinityExtraction318
