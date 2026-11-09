module
public import IntegralGluedTensorSections318
public import InvariantChartCover318
public section
noncomputable section
namespace IntegralGluedDifferentialFrames318
open AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318 IntegralGluedModel318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def branchEmbedding (i : Fin 4) :
    Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c i)) ⟶ scheme R c :=
  Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c i))) ≫ finiteChart R c
instance branchEmbedding_open (i : Fin 4) : IsOpenImmersion (branchEmbedding R c i) :=
  @IsOpenImmersion.comp _ _ _ _ _
    (IsOpenImmersion.of_isLocalization (IntegralBranchDenominatorCover318.denominator R c i))
    (finiteChart_open R c)

theorem branch_structure (i : Fin 4) :
    branchEmbedding R c i ≫ structureMap R c =
      Spec.map (CommRingCat.ofHom (algebraMap R (IntegralBranchCoordinates318.B R c i))) := by
  unfold branchEmbedding
  rw [Category.assoc,finiteChart_structure,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (IsScalarTower.algebraMap_apply R (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c i) r).symm

/-- Actual local trivializations of the intrinsic relative cotangent sheaf
on the constructed integral model, at every original finite contact. -/
@[expose] def branchFrame (h2 : IsUnit (2 : R)) (i : Fin 4) :
    (FamilyIntrinsicDifferentials318.omega (structureMap R c)).restrict
      (branchEmbedding R c i) ≅
        SheafOfModules.unit (Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c i))).ringCatSheaf :=
  (IntrinsicChartNormalization318.iso (branchEmbedding R c i)
    (structureMap R c) (branch_structure R c i)).symm ≪≫
      AffineDifferentialSheaf318.frameIso (IntegralBranchLocalization318.sourceFrame R c i h2)

@[expose] def infinityFrame (h2 : IsUnit (2 : R)) :
    (FamilyIntrinsicDifferentials318.omega (structureMap R c)).restrict (infinityChart R c) ≅
      SheafOfModules.unit (infinityScheme R c).ringCatSheaf :=
  (IntrinsicChartNormalization318.iso (infinityChart R c)
    (structureMap R c) (infinityChart_structure R c)).symm ≪≫
      AffineDifferentialSheaf318.frameIso (IntegralInfinityChart318.frame R c h2)

theorem frames_cover (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R))
    (x : scheme R c) :
    (∃ i,∃ q,branchEmbedding R c i q=x) ∨ (∃ q,infinityChart R c q=x) := by
  rcases charts_cover R c x with ⟨a,rfl⟩|⟨b,hb⟩
  · obtain ⟨i,q,hq⟩ := InvariantChartCover318.finite_localizations_cover
      (IntegralBranchDenominatorCover318.denominator R c)
      (IntegralBranchDenominatorCover318.span_top R c hN) a
    exact Or.inl ⟨i,q,congrArg (finiteChart R c) hq⟩
  · exact Or.inr ⟨b,hb⟩

@[expose] def chart : Option (Fin 4) → Scheme.{u}
  | none => infinityScheme R c
  | some i => Spec (CommRingCat.of (IntegralBranchCoordinates318.B R c i))
@[expose] def embedding : (i : Option (Fin 4)) → chart R c i ⟶ scheme R c
  | none => infinityChart R c
  | some i => branchEmbedding R c i
instance embedding_open (i : Option (Fin 4)) : IsOpenImmersion (embedding R c i) := by
  cases i
  · exact infinityChart_open R c
  · exact branchEmbedding_open R c _

/-- A genuine five-chart open cover of the same integral scheme. The
literal separation integer is retained as the explicit place-coverage condition. -/
@[expose] def cover (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R)) :
    (scheme R c).OpenCover where
  I₀ := Option (Fin 4)
  X := chart R c
  f := embedding R c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro x
    rcases frames_cover R c hN x with ⟨i,q,hq⟩|⟨q,hq⟩
    · exact ⟨some i,q,hq⟩
    · exact ⟨none,q,hq⟩

@[expose] def localFrame (h2 : IsUnit (2 : R)) (i : Option (Fin 4)) :
    (FamilyIntrinsicDifferentials318.omega (structureMap R c)).restrict (embedding R c i) ≅
      SheafOfModules.unit (chart R c i).ringCatSheaf := by
  cases i
  · exact infinityFrame R c h2
  · exact branchFrame R c h2 _
end IntegralGluedDifferentialFrames318
