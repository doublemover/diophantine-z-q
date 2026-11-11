module
public import IntegralGluedModel318
public section
noncomputable section
namespace IntegralGluedChartGeometry318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralSourceBranches318 IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
open IntegralGluedModel318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def branchInclusion :
    Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c 0)) ⟶ finiteScheme R c :=
  Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0)))
instance branchInclusion_open : IsOpenImmersion (branchInclusion R c) :=
  IsOpenImmersion.of_isLocalization (IntegralBranchDenominatorCover318.denominator R c 0)
@[expose] def branchChart :
    Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c 0)) ⟶ scheme R c :=
  branchInclusion R c ≫ finiteChart R c
instance branchChart_open : IsOpenImmersion (branchChart R c) := by unfold branchChart;infer_instance
@[expose] def overlapChart : commonScheme R c ⟶ scheme R c :=
  intoFinite R c ≫ finiteChart R c
instance overlapChart_open : IsOpenImmersion (overlapChart R c) := by unfold overlapChart;infer_instance

theorem finite_factor : Spec.map (CommRingCat.ofHom (finiteMap R c).toRingHom) ≫
    branchInclusion R c = intoFinite R c := by
  unfold branchInclusion intoFinite
  rw [←Spec.map_comp]
  rfl

theorem branch_route : Spec.map (CommRingCat.ofHom (finiteMap R c).toRingHom) ≫
    branchChart R c = overlapChart R c := by
  rw [branchChart,←Category.assoc,finite_factor]
  rfl

theorem infinity_route : Spec.map (CommRingCat.ofHom (infinityMap R c).toRingHom) ≫
    infinityChart R c = overlapChart R c := pushout.condition.symm

theorem overlap_over_base : overlapChart R c ≫ structureMap R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (Overlap R c))) := by
  rw [overlapChart,Category.assoc,finiteChart_structure]
  unfold intoFinite
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (sourceMap R c).commutes

theorem branch_over_base : branchChart R c ≫ structureMap R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (IntegralBranchCoordinates318.B R c 0))) := by
  rw [branchChart,Category.assoc,finiteChart_structure]
  unfold branchInclusion
  rw [←Spec.map_comp]
  congr 1

theorem branchLE : overlapChart R c ''ᵁ ⊤ ≤ branchChart R c ''ᵁ ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  change Set.range (overlapChart R c) ⊆ Set.range (branchChart R c)
  rintro _ ⟨z,rfl⟩
  exact ⟨Spec.map (CommRingCat.ofHom (finiteMap R c).toRingHom) z,
    congrArg (fun f => f z) (branch_route R c)⟩
theorem infinityLE : overlapChart R c ''ᵁ ⊤ ≤ infinityChart R c ''ᵁ ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  change Set.range (overlapChart R c) ⊆ Set.range (infinityChart R c)
  rintro _ ⟨z,rfl⟩
  exact ⟨Spec.map (CommRingCat.ofHom (infinityMap R c).toRingHom) z,
    congrArg (fun f => f z) (infinity_route R c)⟩

/-- The computed principal overlap is the FULL branch-zero/infinity
intersection inside the actual whole-source gluing. -/
theorem full_intersection : Set.range (overlapChart R c) =
    Set.range (branchChart R c) ∩ Set.range (infinityChart R c) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    exact ⟨⟨Spec.map (CommRingCat.ofHom (finiteMap R c).toRingHom) z,
      congrArg (fun f => f z) (branch_route R c)⟩,
      ⟨Spec.map (CommRingCat.ofHom (infinityMap R c).toRingHom) z,
      congrArg (fun f => f z) (infinity_route R c)⟩⟩
  · rintro x ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    have he : finiteChart R c (branchInclusion R c a)=infinityChart R c b :=
      ha.trans hb.symm
    obtain ⟨z,hz,_⟩ := GenericOpenPushout318.exists_overlap
      (intoFinite R c) (intoInfinity R c) (branchInclusion R c a) b he
    refine ⟨z,?_⟩
    change finiteChart R c (intoFinite R c z)=x
    rw [hz]
    exact ha
end IntegralGluedChartGeometry318
