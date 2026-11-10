module
public import IntegralBranchTensorTransport318
public section
noncomputable section
namespace IntegralAllBranchChartGeometry318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralSourceBranches318 IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
open IntegralGluedModel318 IntegralGluedChartGeometry318 IntegralGluedDifferentialFrames318
open IntegralAllBranchOverlapMaps318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

/-- Every actual finite chart uses the same specified overlap map into the
whole-source pushout. All four original coordinates retain their identities. -/
theorem branch_route (i : Fin 4) :
    Spec.map (CommRingCat.ofHom (branchMap R c i).toRingHom) ≫
      branchEmbedding R c i = overlapChart R c := by
  unfold branchEmbedding overlapChart
  rw [←Category.assoc]
  congr 1
  unfold intoFinite
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact branchMap_source R c i

theorem branchLE (i : Fin 4) : overlapChart R c ''ᵁ ⊤ ≤ branchEmbedding R c i ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  change Set.range (overlapChart R c) ⊆ Set.range (branchEmbedding R c i)
  rintro x ⟨z,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (branchMap R c i).toRingHom) z,?_⟩
  exact congrArg (fun f => f z) (branch_route R c i)

/-- The overlap is the FULL finite/infinity intersection for every contact,
not merely an open on which the coefficient formulas happen to agree. -/
theorem full_infinity_intersection (i : Fin 4) :
    Set.range (overlapChart R c) =
      Set.range (branchEmbedding R c i) ∩ Set.range (infinityChart R c) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    exact ⟨⟨Spec.map (CommRingCat.ofHom (branchMap R c i).toRingHom) z,
      congrArg (fun f => f z) (branch_route R c i)⟩,
      ⟨Spec.map (CommRingCat.ofHom (infinityMap R c).toRingHom) z,
      congrArg (fun f => f z) (infinity_route R c)⟩⟩
  · rintro x ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    have he : finiteChart R c
        (Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c)
          (IntegralBranchCoordinates318.B R c i))) a) = infinityChart R c b :=
      ha.trans hb.symm
    obtain ⟨z,hz,_⟩ := GenericOpenPushout318.exists_overlap
      (intoFinite R c) (intoInfinity R c) _ b he
    refine ⟨z,?_⟩
    change finiteChart R c (intoFinite R c z)=x
    rw [hz]
    exact ha

theorem branch_P (i : Fin 4) :
    branchMap R c i (IntegralBranchBicanonical318.sourceP R c i)=P R c :=
  branchMap_polynomial R c i _
theorem branch_t (i : Fin 4) :
    branchMap R c i (IntegralBranchCoordinates318.sourceT R c i)=t R c :=
  branchMap_polynomial R c i _

/-- All four original finite J² pairs coincide on the literal pushout
overlap in the genuine intrinsic tensor sheaf of that integral model. -/
theorem common_pair (i k : Fin 4) (n : Fin 2) :
    IntrinsicTensorChartSections318.weightedSquare (overlapChart R c) (structureMap R c)
      (overlap_over_base R c)
      (branchMap R c i ((VerticalSection318.J : IntegralBranchCoordinates318.B R c i)^2 *
        (if n=0 then IntegralBranchBicanonical318.coefficient0 R c i
          else IntegralBranchBicanonical318.coefficient1 R c i)))
      (IntegralBranchTensorTransport318.differential R c i (branchMap R c i)) =
    IntrinsicTensorChartSections318.weightedSquare (overlapChart R c) (structureMap R c)
      (overlap_over_base R c)
      (branchMap R c k ((VerticalSection318.J : IntegralBranchCoordinates318.B R c k)^2 *
        (if n=0 then IntegralBranchBicanonical318.coefficient0 R c k
          else IntegralBranchBicanonical318.coefficient1 R c k)))
      (IntegralBranchTensorTransport318.differential R c k (branchMap R c k)) := by
  apply IntegralBranchTensorTransport318.scaled_agreement
  · rw [branch_P,branch_P]
  · rw [branch_t,branch_t]
  · rw [branch_P]; exact P_unit R c
end IntegralAllBranchChartGeometry318
