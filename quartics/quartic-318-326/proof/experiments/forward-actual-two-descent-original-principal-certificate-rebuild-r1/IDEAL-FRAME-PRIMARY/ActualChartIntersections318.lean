module
public import GlobalInvariantCompatibility318
import all WeierstrassGluing318
public section
noncomputable section
namespace ActualChartIntersections318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : Type u} [CommRing S]

/-- The genuine product localization has exactly the full intersection image. -/
theorem product_image (x y : S) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (x*y))))) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))) ∩
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away y)))) := by
  change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (x*y)))) =
    Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away x))) ∩
    Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away y)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (x*y)) (x*y),
    PrimeSpectrum.localization_away_comap_range (Localization.Away x) x,
    PrimeSpectrum.localization_away_comap_range (Localization.Away y) y,
    PrimeSpectrum.basicOpen_mul]
  rfl

variable {R : Type u} [CommRing R]

/-- The checked x/y common ring covers the full intersection of the actual finite
Jacobian chart images inside the globally glued Weierstrass scheme. -/
theorem finite_image (A B : R) :
    Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassOverlap318.Affine A B) (FiniteInvariantDifferential318.CommonRing A B))) ≫
        WeierstrassGluing318.finiteChart A B) =
      Set.range (InvariantChartCover318.finiteInto A B 0) ∩
        Set.range (InvariantChartCover318.finiteInto A B 1) := by
  let f := WeierstrassGluing318.finiteChart A B
  have hi : Function.Injective f := f.isOpenEmbedding.injective
  have h := product_image
    (ShortAffineJacobian318.presentation A B 0).jacobian
    (ShortAffineJacobian318.presentation A B 1).jacobian
  change Set.range (f ∘ Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassOverlap318.Affine A B) (FiniteInvariantDifferential318.CommonRing A B)))) =
    Set.range (f ∘ Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassOverlap318.Affine A B) (WeierstrassKaehler318.AffineChart A B 0)))) ∩
    Set.range (f ∘ Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassOverlap318.Affine A B) (WeierstrassKaehler318.AffineChart A B 1))))
  rw [Set.range_comp,Set.range_comp,Set.range_comp,h,Set.image_inter hi]
end ActualChartIntersections318

namespace ActualChartIntersections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The original two-chart scheme pushout identifies points precisely along the
actual finite/infinity overlap, so this is not merely a common subopen. -/
theorem original_overlap_points (A B : R)
    (a : ShortAffineScheme318.scheme A B) (b : InfinitySmooth318.scheme A B) :
    WeierstrassGluing318.finiteChart A B a = WeierstrassGluing318.infinityChart A B b ↔
      ∃ q : WeierstrassGluing318.overlap A B,
        WeierstrassGluing318.intoAffine A B q=a ∧ WeierstrassGluing318.intoInfinity A B q=b := by
  change colimit.ι (span (WeierstrassGluing318.intoAffine A B)
      (WeierstrassGluing318.intoInfinity A B)) WalkingSpan.left a =
    colimit.ι (span (WeierstrassGluing318.intoAffine A B)
      (WeierstrassGluing318.intoInfinity A B)) WalkingSpan.right b ↔ _
  rw [Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨k,fi,fj,q,hi,hj⟩
    cases k with
    | none =>
      cases fi
      cases fj
      exact ⟨q,hi,hj⟩
    | some i =>
      cases i with
      | left => cases fj
      | right => cases fi
  · rintro ⟨q,hq,hq'⟩
    exact ⟨WalkingSpan.zero,WalkingSpan.Hom.fst,WalkingSpan.Hom.snd,q,hq,hq'⟩
end ActualChartIntersections318
