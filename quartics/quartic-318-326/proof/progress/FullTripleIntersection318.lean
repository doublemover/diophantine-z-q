module
public import FullInfinityIntersection318
import all WeierstrassGluing318
public section
noncomputable section
namespace FullTripleIntersection318
open AlgebraicGeometry CategoryTheory
open WeierstrassOverlap318 DifferentialChartMaps318 ActualDifferentialTriple318
open InvariantChartCover318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

@[expose] def into (A B : R) : Spec (CommRingCat.of (Triple A B)) ⟶
    WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (R:=ActualDifferentialTriple318.FI A B) (S:=ActualDifferentialTriple318.Triple A B) (fromFI A B).toRingHom) ≫ FullInfinityIntersection318.into A B

theorem y_route (A B : R) :
    Spec.map (CommRingCat.ofHom (R:=DifferentialChartMaps318.FiniteChart A B) (S:=ActualDifferentialTriple318.Triple A B) (fromY A B).toRingHom) ≫ finiteInto A B 1 = into A B := by
  rw [fromY,TripleOpen318.spec_comp,Category.assoc,FullInfinityIntersection318.finite_route]
  rfl

theorem infinity_route (A B : R) :
    Spec.map (CommRingCat.ofHom (R:=DifferentialChartMaps318.InfinityChart A B) (S:=ActualDifferentialTriple318.Triple A B) (fromInfinity A B).toRingHom) ≫ infinityInto A B = into A B := by
  rw [fromInfinity,TripleOpen318.spec_comp,Category.assoc,FullInfinityIntersection318.infinity_route]
  rfl

theorem x_route (A B : R) :
    Spec.map (CommRingCat.ofHom (R:=FiniteInvariantDifferential318.XChart A B) (S:=ActualDifferentialTriple318.Triple A B) (fromX A B).toRingHom) ≫ finiteInto A B 0 = into A B := by
  let fx : CommRingCat.of (Affine A B) ⟶ CommRingCat.of (FiniteInvariantDifferential318.XChart A B) :=
    CommRingCat.ofHom (algebraMap (Affine A B) (FiniteInvariantDifferential318.XChart A B))
  let fy : CommRingCat.of (Affine A B) ⟶ CommRingCat.of (FiniteChart A B) :=
    CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B))
  let gx : CommRingCat.of (FiniteInvariantDifferential318.XChart A B) ⟶ CommRingCat.of (Triple A B) :=
    CommRingCat.ofHom (fromX A B).toRingHom
  let gy : CommRingCat.of (FiniteChart A B) ⟶ CommRingCat.of (Triple A B) :=
    CommRingCat.ofHom (fromY A B).toRingHom
  have hr : fx ≫ gx=fy ≫ gy := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change fromX A B (algebraMap (Affine A B) (FiniteInvariantDifferential318.XChart A B) a)=
      fromY A B (algebraMap (Affine A B) (FiniteChart A B) a)
    simp only [fromX,fromY,AlgHom.comp_apply,FiniteInvariantDifferential318.xMap,
      ProductLocalization318.leftMap_integral,fromXY_integral,finiteChartMap_integral]
    rfl
  have hs : Spec.map gx ≫ Spec.map fx=Spec.map gy ≫ Spec.map fy :=
    (Spec.map_comp fx gx).symm.trans ((congrArg Spec.map hr).trans (Spec.map_comp fy gy))
  calc
    _ = (Spec.map gx ≫ Spec.map fx) ≫ WeierstrassGluing318.finiteChart A B :=
      (Category.assoc _ _ _).symm
    _ = (Spec.map gy ≫ Spec.map fy) ≫ WeierstrassGluing318.finiteChart A B :=
      congrArg (fun f => f ≫ WeierstrassGluing318.finiteChart A B) hs
    _ = Spec.map gy ≫ finiteInto A B 1 := Category.assoc _ _ _
    _ = into A B := y_route A B

/-- The actual triple localization covers exactly the intersection of the x-chart
with the full finite-y/infinity overlap. -/
theorem full_image (A B : R) : Set.range (into A B)=
    Set.range (finiteInto A B 0) ∩ Set.range (FullInfinityIntersection318.into A B) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q,rfl⟩
    exact ⟨⟨Spec.map (CommRingCat.ofHom (R:=FiniteInvariantDifferential318.XChart A B) (S:=ActualDifferentialTriple318.Triple A B) (fromX A B).toRingHom) q,
      congrArg (fun f => f q) (x_route A B)⟩,
      ⟨Spec.map (CommRingCat.ofHom (R:=ActualDifferentialTriple318.FI A B) (S:=ActualDifferentialTriple318.Triple A B) (fromFI A B).toRingHom) q,rfl⟩⟩
  · rintro p ⟨⟨a,ha⟩,⟨q,hq⟩⟩
    let a0 := Spec.map (CommRingCat.ofHom (algebraMap (Affine A B)
      (FiniteInvariantDifferential318.XChart A B))) a
    let b0 := Spec.map (CommRingCat.ofHom (finiteBaseMap A B).toRingHom) q
    have hb : WeierstrassGluing318.finiteChart A B b0=p := by
      rw [←FullInfinityIntersection318.finite_route] at hq
      change (Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B))) ≫
          WeierstrassGluing318.finiteChart A B) q=p at hq
      have he : Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B))) =
          Spec.map (CommRingCat.ofHom (finiteBaseMap A B).toRingHom) := by
        rw [←Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        exact finiteChartMap_integral A B
      rw [←Category.assoc,he] at hq
      exact hq
    have hab : a0=b0 := (WeierstrassGluing318.finiteChart A B).isOpenEmbedding.injective
      (ha.trans hb.symm)
    have hx := FullInfinityIntersection318.localization_avoids
      (ShortAffineJacobian318.presentation A B 0).jacobian a
    change (ShortAffineJacobian318.presentation A B 0).jacobian ∉ a0.asIdeal at hx
    rw [hab] at hx
    change extraMinor A B ∉ q.asIdeal at hx
    obtain ⟨c,hc⟩ := InvariantChartCover318.localization_preimage _ q hx
    exact ⟨c,congrArg (FullInfinityIntersection318.into A B) hc |>.trans hq⟩

/-- Invertibility of the actual discriminant forces 2 to be invertible. -/
theorem two_unit (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) : IsUnit (2:R) := by
  have h16 : IsUnit ((2:R)^4) := by
    convert (isUnit_of_mul_isUnit_left hD).neg using 1 <;> norm_num
  exact (isUnit_pow_iff (by decide : 4 ≠ 0)).mp h16

/-- On the original finite/infinity overlap, 2y is invertible when the
Weierstrass discriminant is a unit. -/
theorem overlap_y_unit (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    IsUnit (toInfinityBase A B (ShortAffineJacobian318.presentation A B 1).jacobian) := by
  rw [ShortAffineJacobian318.jacobian_y,map_mul,map_ofNat,toInfinityBase_y]
  have h2 : IsUnit (2 : InfinityOverlap A B) := by
    exact map_ofNat (algebraMap R (InfinityOverlap A B)) 2 ▸ (two_unit A B hD).map (algebraMap R (InfinityOverlap A B))
  exact h2.mul (IsUnit.of_mul_eq_one_right (iz A B) (iz_ii A B))

/-- Every finite/infinity intersection point lies in the finite-y Jacobian chart
under the actual smooth discriminant hypothesis. -/
theorem overlap_in_y (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (p : WeierstrassGluing318.scheme A B)
    (ha : p ∈ Set.range (finiteInto A B 0)) (hb : p ∈ Set.range (infinityInto A B)) :
    p ∈ Set.range (finiteInto A B 1) := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  let a0 := Spec.map (CommRingCat.ofHom (algebraMap (Affine A B)
    (FiniteInvariantDifferential318.XChart A B))) a
  let b0 := Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityChart A B))) b
  have he : WeierstrassGluing318.finiteChart A B a0 =
      WeierstrassGluing318.infinityChart A B b0 := ha.trans hb.symm
  obtain ⟨q,hqA,_⟩ := (ActualChartIntersections318.original_overlap_points A B a0 b0).mp he
  have hy : (ShortAffineJacobian318.presentation A B 1).jacobian ∉ a0.asIdeal := by
    rw [←hqA,WeierstrassGluing318.intoAffine_eq]
    change toInfinityBase A B (ShortAffineJacobian318.presentation A B 1).jacobian ∉ q.asIdeal
    intro hm
    exact q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hm (overlap_y_unit A B hD))
  obtain ⟨c,hc⟩ := InvariantChartCover318.localization_preimage _ a0 hy
  exact ⟨c,congrArg (WeierstrassGluing318.finiteChart A B) hc |>.trans ha⟩

/-- The checked three-chart ring is the full x/infinity pairwise intersection,
not merely a dense part, for the smooth actual family. -/
theorem full_x_infinity (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    Set.range (into A B)=Set.range (finiteInto A B 0) ∩ Set.range (infinityInto A B) := by
  rw [full_image,FullInfinityIntersection318.full_image]
  ext p
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,overlap_in_y A B hD p h.1 h.2,h.2⟩
end FullTripleIntersection318
