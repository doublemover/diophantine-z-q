module
public import WeierstrassChartPullback318
import all WeierstrassGluing318
public section
noncomputable section
namespace ChartInputEquality318
open AlgebraicGeometry CategoryTheory
open WeierstrassOverlap318
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem overlap_hom_exists (A B:R) (φ:Affine A B →ₐ[R] S) (ψ:Infinity A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B) :
    ∃κ:InfinityOverlap A B →+* S,
      (∀r,κ (toInfinityBase A B r)=φ r) ∧
      (∀r,κ (algebraMap (Infinity A B) (InfinityOverlap A B) r)=ψ r) := by
  let k:=WeierstrassChartPullback318.lift A B
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) h
  obtain ⟨κ,hκ⟩:=Spec.map_surjective k
  have hf:=WeierstrassChartPullback318.lift_finite A B
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) h
  have hi:=WeierstrassChartPullback318.lift_infinity A B
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) h
  change k ≫ _=_ at hf hi
  rw [←hκ,WeierstrassGluing318.intoAffine_eq,←Spec.map_comp] at hf
  rw [←hκ] at hi
  change Spec.map κ ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (Infinity A B) (InfinityOverlap A B)))=_ at hi
  rw [←Spec.map_comp] at hi
  refine ⟨κ.hom,?_,?_⟩
  · intro r
    exact congrArg (fun k=>k.hom r) (Spec.map_injective hf)
  · intro r
    exact congrArg (fun k=>k.hom r) (Spec.map_injective hi)

/-- Equality of the actual finite/infinity Scheme inputs forces the literal
coordinate transition equations over every coefficient algebra. -/
theorem finite_infinity (A B:R) (φ:Affine A B →ₐ[R] S) (ψ:Infinity A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B) :
    ψ (InfinityChart318.x A B)*φ (ShortAffineJacobian318.y A B)=φ (ShortAffineJacobian318.x A B) ∧
    ψ (InfinityChart318.z A B)*φ (ShortAffineJacobian318.y A B)=1 := by
  obtain ⟨κ,hf,hi⟩:=overlap_hom_exists A B φ ψ h
  have hx:=hf (ShortAffineJacobian318.x A B)
  have hy:=hf (ShortAffineJacobian318.y A B)
  simp only [toInfinityBase_x,toInfinityBase_y,map_mul] at hx hy
  constructor
  · rw [←hi,←hy]
    exact hx
  · rw [←hi,←hy,←map_mul]
    exact (congrArg κ (iz_ii A B)).trans (map_one κ)

theorem finite_injective (A B:R) (φ ψ:Affine A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B) : φ=ψ := by
  apply AlgHom.ext
  intro r
  exact congrArg (fun k=>k.hom r) (Spec.map_injective ((cancel_mono (WeierstrassGluing318.finiteChart A B)).mp h))
theorem infinity_injective (A B:R) (φ ψ:Infinity A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B) : φ=ψ := by
  apply AlgHom.ext
  intro r
  exact congrArg (fun k=>k.hom r) (Spec.map_injective ((cancel_mono (WeierstrassGluing318.infinityChart A B)).mp h))
end ChartInputEquality318
