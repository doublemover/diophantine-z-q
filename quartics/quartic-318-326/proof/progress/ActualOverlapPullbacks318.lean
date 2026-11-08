module
public import FullTripleIntersection318
public section
noncomputable section
namespace ActualOverlapPullbacks318
open AlgebraicGeometry CategoryTheory
open InvariantChartCover318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- A proved full intersection image upgrades an actual commuting open square to
an actual categorical pullback of schemes. -/
theorem of_full_image {U X Y Z : Scheme.{u}}
    (a : U ⟶ X) (b : U ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion i] [IsOpenImmersion j]
    (h : a ≫ i=b ≫ j)
    (hfull : Set.range (a ≫ i)=Set.range i ∩ Set.range j) :
    IsPullback a b i j := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback b a j i h
  ext p
  change i p ∈ Set.range j ↔ p ∈ Set.range a
  constructor
  · intro hp
    have hi : i p ∈ Set.range (a ≫ i) := by
      rw [hfull]
      exact ⟨⟨p,rfl⟩,hp⟩
    obtain ⟨q,hq⟩ := hi
    exact ⟨q,i.isOpenEmbedding.injective hq⟩
  · rintro ⟨q,rfl⟩
    exact ⟨b q,congrArg (fun f => f q) h.symm⟩

variable {R : Type u} [CommRing R]

/-- The actual finite/infinity differential common ring is their actual scheme
fiber product, so the canonical restriction comparison is on the full overlap. -/
theorem finite_infinity (A B : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (DifferentialChartMaps318.finiteChartMap A B).toRingHom))
      (Spec.map (CommRingCat.ofHom (DifferentialChartMaps318.infinityChartMap A B).toRingHom))
      (finiteInto A B 1) (infinityInto A B) := by
  letI := ActualInfinityOpen318.finite_open A B
  apply of_full_image
  · exact (FullInfinityIntersection318.finite_route A B).trans
      (FullInfinityIntersection318.infinity_route A B).symm
  · rw [FullInfinityIntersection318.finite_route]
    exact FullInfinityIntersection318.full_image A B

/-- Under the actual discriminant condition, the actual three-chart localization
is the entire x/infinity scheme fiber product. -/
theorem x_infinity (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (R:=FiniteInvariantDifferential318.XChart A B) (S:=ActualDifferentialTriple318.Triple A B) (ActualDifferentialTriple318.fromX A B).toRingHom))
      (Spec.map (CommRingCat.ofHom (R:=DifferentialChartMaps318.InfinityChart A B) (S:=ActualDifferentialTriple318.Triple A B) (ActualDifferentialTriple318.fromInfinity A B).toRingHom))
      (finiteInto A B 0) (infinityInto A B) := by
  letI := TripleOpen318.fromX_open A B
  apply of_full_image
  · exact (FullTripleIntersection318.x_route A B).trans
      (FullTripleIntersection318.infinity_route A B).symm
  · rw [FullTripleIntersection318.x_route]
    exact FullTripleIntersection318.full_x_infinity A B hD

theorem finite_x_route (A B : R) :
    Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.xMap A B).toRingHom) ≫
      finiteInto A B 0 =
    Spec.map (CommRingCat.ofHom (algebraMap (WeierstrassOverlap318.Affine A B)
      (FiniteInvariantDifferential318.CommonRing A B))) ≫ WeierstrassGluing318.finiteChart A B := by
  unfold finiteInto
  rw [←Category.assoc]
  congr 1
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact ProductLocalization318.leftMap_integral _ _

theorem finite_y_route (A B : R) :
    Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.yMap A B).toRingHom) ≫
      finiteInto A B 1 =
    Spec.map (CommRingCat.ofHom (algebraMap (WeierstrassOverlap318.Affine A B)
      (FiniteInvariantDifferential318.CommonRing A B))) ≫ WeierstrassGluing318.finiteChart A B := by
  unfold finiteInto
  rw [←Category.assoc]
  congr 1
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact ProductLocalization318.rightMap_integral _ _

/-- The actual product localization is the entire finite x/y scheme fiber product. -/
theorem finite_finite (A B : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.xMap A B).toRingHom))
      (Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.yMap A B).toRingHom))
      (finiteInto A B 0) (finiteInto A B 1) := by
  letI := FiniteOverlapSheaves318.x_open A B
  apply of_full_image
  · exact (finite_x_route A B).trans (finite_y_route A B).symm
  · rw [finite_x_route]
    exact ActualChartIntersections318.finite_image A B
end ActualOverlapPullbacks318
