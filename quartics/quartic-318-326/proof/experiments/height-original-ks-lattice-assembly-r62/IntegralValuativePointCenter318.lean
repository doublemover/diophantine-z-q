module
public import IntegralValuativeInfinityExtension318
public import IntegralValuativeBranchSelection318
public section
noncomputable section
namespace IntegralValuativePointCenter318
open Polynomial IntegralSourceBranches318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))

/-- Every specified original four-root field point has an actual center on
the original integral model over its valuation ring. The same generic point
is retained on either complete original chart, with every sign unchanged. -/
theorem exists_extension :
    ∃ g : Spec (CommRingCat.of V) ⟶ IntegralGluedModel318.scheme V c,
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g=
        IntegralValuativeGenericPoint318.point V K c t y hy ∧
      g ≫ IntegralGluedModel318.structureMap V c=𝟙 _ := by
  by_cases ht : IsLocalization.IsInteger V t
  · obtain ⟨a,ha⟩ := ht
    obtain ⟨z,hz,hz2⟩ := IntegralValuativeRootCoordinates318.finite_coordinates V K c t y hy a ha
    exact ⟨IntegralValuativeChartPoints318.finitePoint V c a z hz2,
      IntegralValuativeGenericPoint318.finite_point_extension V K c t y hy a z hz2 ha hz,
      IntegralValuativeChartPoints318.finitePoint_structure V c a z hz2⟩
  · obtain ⟨u,z,hu,hz,hun,hz2,hd⟩ :=
      IntegralValuativeRootCoordinates318.infinity_coordinates V K c t y hy ht
    exact ⟨IntegralValuativeChartPoints318.infinityPoint V c u z hz2 hd,
      IntegralValuativeInfinityExtension318.infinity_point_extension V K c t y hy ht u z hz2 hd hu hz,
      IntegralValuativeChartPoints318.infinityPoint_structure V c u z hz2 hd⟩

/-- A chosen center is selected only after proving extension of the actual
input point. Its generic specialization is not an extra hypothesis. -/
@[expose] def center : Spec (CommRingCat.of V) ⟶ IntegralGluedModel318.scheme V c :=
  Classical.choose (exists_extension V K c t y hy)

theorem center_generic :
    Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ center V K c t y hy=
      IntegralValuativeGenericPoint318.point V K c t y hy :=
  (Classical.choose_spec (exists_extension V K c t y hy)).1

theorem center_over_base : center V K c t y hy ≫ IntegralGluedModel318.structureMap V c=𝟙 _ :=
  (Classical.choose_spec (exists_extension V K c t y hy)).2

/-- If t is integral, the same field point has a genuine contact-chart map
into V on the good coefficient base. The full cover chooses the chart rather
than a caller supplying an invertible original denominator. -/
theorem finite_branch_center (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : V))
    (ht : IsLocalization.IsInteger V t) :
    ∃ (i : Fin 4) (f : IntegralBranchCoordinates318.B V c i →+* V),
      (∀ a : SourceOrder V c,
        algebraMap V K (f (algebraMap (SourceOrder V c) (IntegralBranchCoordinates318.B V c i) a))=
          IntegralValuativeGenericPoint318.sourceMap V K c t y hy a) ∧
      algebraMap V K (f (IntegralBranchCoordinates318.sourceCoordinate V c i))=y i := by
  obtain ⟨a,ha⟩ := ht
  obtain ⟨z,hz,hz2⟩ := IntegralValuativeRootCoordinates318.finite_coordinates V K c t y hy a ha
  let f := IntegralValuativeChartPoints318.finiteMap V c a z hz2
  obtain ⟨i,hi⟩ := IntegralValuativeBranchSelection318.branch_exists V c f hN
  refine ⟨i,IntegralValuativeBranchSelection318.branchMap V c f i hi,?_,?_⟩
  · intro b
    rw [IntegralValuativeBranchSelection318.branchMap_source]
    exact RingHom.congr_fun
      (IntegralValuativeGenericPoint318.finite_generic_equality V K c t y hy a z hz2 ha hz) b
  · rw [IntegralValuativeBranchSelection318.branchMap_root]
    change algebraMap V K (IntegralValuativeChartPoints318.finiteMap V c a z hz2
      (FourRootOrderSigns318.generator (coefficient V c) i))=y i
    rw [IntegralValuativeChartPoints318.finiteMap_generator,hz]
end IntegralValuativePointCenter318
