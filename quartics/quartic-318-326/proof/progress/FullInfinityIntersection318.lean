module
public import ActualChartIntersections318
import all WeierstrassGluing318
public section
noncomputable section
namespace FullInfinityIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassOverlap318 DifferentialChartMaps318 ActualDifferentialOverlap318
open InvariantChartCover318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- The actual common localization mapped into the genuine glued curve. -/
@[expose] def into (A B : R) : Spec (CommRingCat.of (CommonRing A B)) ⟶
    WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B))) ≫
    WeierstrassGluing318.intoInfinity A B ≫ WeierstrassGluing318.infinityChart A B

theorem finite_route (A B : R) :
    Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom) ≫ finiteInto A B 1 = into A B := by
  unfold finiteInto into
  rw [←Category.assoc]
  have he : Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B))) =
      Spec.map (CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B))) ≫
        WeierstrassGluing318.intoAffine A B := by
    rw [WeierstrassGluing318.intoAffine_eq,←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact finiteChartMap_integral A B
  rw [he,Category.assoc]
  congr 1
  exact pushout.condition

theorem infinity_route (A B : R) :
    Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom) ≫ infinityInto A B = into A B := by
  unfold infinityInto into
  rw [←Category.assoc]
  have he : Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityChart A B))) =
      Spec.map (CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B))) ≫
        WeierstrassGluing318.intoInfinity A B := by
    unfold WeierstrassGluing318.intoInfinity
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (infinityChartMap_integral A B a).trans
      (IsScalarTower.algebraMap_apply (Infinity A B) (InfinityOverlap A B) (CommonRing A B) a).symm
  rw [he,Category.assoc]

/-- Every point of a principal localization avoids its inverted denominator. -/
theorem localization_avoids {S : Type u} [CommRing S] (s : S)
    (p : Spec (CommRingCat.of (Localization.Away s))) :
    s ∉ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) p).asIdeal := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) p ∈
      Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s))) := ⟨p,rfl⟩
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s] at h
  exact h

/-- The actual finite-y/infinity common ring covers the full intersection of the
actual two differential charts in the global scheme, over any base ring. -/
theorem full_image (A B : R) : Set.range (into A B) =
    Set.range (finiteInto A B 1) ∩ Set.range (infinityInto A B) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q,rfl⟩
    exact ⟨⟨Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom) q,
      congrArg (fun f => f q) (finite_route A B)⟩,
      ⟨Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom) q,
      congrArg (fun f => f q) (infinity_route A B)⟩⟩
  · rintro p ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    let a0 := Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B))) a
    let b0 := Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityChart A B))) b
    have hbase : WeierstrassGluing318.finiteChart A B a0 =
        WeierstrassGluing318.infinityChart A B b0 := ha.trans hb.symm
    obtain ⟨q,hqA,hqB⟩ := (ActualChartIntersections318.original_overlap_points A B a0 b0).mp hbase
    have hy := localization_avoids (ShortAffineJacobian318.presentation A B 1).jacobian a
    change (ShortAffineJacobian318.presentation A B 1).jacobian ∉ a0.asIdeal at hy
    rw [←hqA,WeierstrassGluing318.intoAffine_eq] at hy
    change toInfinityBase A B (ShortAffineJacobian318.presentation A B 1).jacobian ∉ q.asIdeal at hy
    rw [ShortAffineJacobian318.jacobian_y,map_mul,map_ofNat,toInfinityBase_y] at hy
    have hj := localization_avoids (InfinityChart318.presentation A B).jacobian b
    change (InfinityChart318.presentation A B).jacobian ∉ b0.asIdeal at hj
    rw [←hqB] at hj
    change actualJacobian A B ∉ q.asIdeal at hj
    have hd : actualJacobian A B*(2*ii A B) ∉ q.asIdeal := by
      simpa only [q.isPrime.mul_mem_iff_mem_or_mem,not_or] using And.intro hj hy
    obtain ⟨c,hc⟩ := InvariantChartCover318.localization_preimage _ q hd
    refine ⟨c,?_⟩
    change WeierstrassGluing318.infinityChart A B
      (WeierstrassGluing318.intoInfinity A B
        (Spec.map (CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B))) c))=p
    rw [hc,hqB]
    exact hb
end FullInfinityIntersection318
