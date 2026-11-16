module
public import OriginalTensorPullbackGaugeNormalization318
public section
noncomputable section
namespace OriginalTensorPullbackFrameIndependence318
open AlgebraicGeometry CategoryTheory
open OriginalTensorPullbackGaugeNormalization318
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  (M N : Y.Modules)
  (em em' : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en en' : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- The original tensor-pullback comparison is independent of ALL frame
choices on the same genuine cover. Both sides are actual reconstructed
maps; no monoidal naturality or independent-cover invariance is assumed. -/
lemma comparison :
    TensorPullbackCocycle318.comparison p U M N em en hc=
      TensorPullbackCocycle318.comparison p U M N em' en' hc := by
  let a := fun i => OriginalModuleFrameRatio318.ratio (em i) (em' i)
  let b := fun i => OriginalModuleFrameRatio318.ratio (en i) (en' i)
  have ha (i : ι) : StructureLineAutomorphisms318.iso (U i).toScheme (a i) ≪≫ em i=em' i :=
    OriginalModuleFrameRatio318.action (em i) (em' i)
  have hb (i : ι) : StructureLineAutomorphisms318.iso (U i).toScheme (b i) ≪≫ en i=en' i :=
    OriginalModuleFrameRatio318.action (en i) (en' i)
  let s := fun i => StructureLineAutomorphisms318.iso (p ⁻¹ᵁ U i).toScheme
    (OriginalFramePullbackUnits318.units (LinePullbackFrames318.chartMap p (U i)) (a i*b i))
  have hs (i : ι) : sourceFrame p M N (U i) (em' i) (en' i)=
      s i ≪≫ sourceFrame p M N (U i) (em i) (en i) := by
    rw [←ha i,←hb i]
    exact source_action p M N (U i) (em i) (en i) (a i) (b i)
  have ht (i : ι) : targetFrame p M N (U i) (em' i) (en' i)=
      s i ≪≫ targetFrame p M N (U i) (em i) (en i) := by
    rw [←ha i,←hb i]
    exact target_action p M N (U i) (em i) (en i) (a i) (b i)
  apply Iso.ext
  apply OriginalFramedComparisonNormalization318.hom_ext_restrict _
    (fun i => p ⁻¹ᵁ U i) (fun i => targetFrame p M N (U i) (em i) (en i))
    (LinePullbackFrames318.preimage_cover p U hc)
  intro i
  apply (cancel_epi (sourceFrame p M N (U i) (em i) (en i)).hom).mp
  have h := congrArg Iso.hom
    (OriginalTensorPullbackFrameNormalization318.frame p U M N em en hc i)
  have h' := OriginalTensorPullbackFrameNormalization318.frame p U M N em' en' hc i
  change sourceFrame p M N (U i) (em' i) (en' i) ≪≫ _=
    targetFrame p M N (U i) (em' i) (en' i) at h'
  rw [hs,ht] at h'
  have hh := congrArg Iso.hom h'
  simp only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc] at hh
  have hh' := (cancel_epi (s i).hom).mp hh
  exact h.trans hh'.symm
end OriginalTensorPullbackFrameIndependence318
