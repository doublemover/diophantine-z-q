module
public import OriginalTensorPullbackFrameNormalization318
public section
noncomputable section
namespace OriginalTensorPullbackNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  {M N M' N' : Y.Modules} (a : M ≅ M') (b : N ≅ N')
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- Naturality of the ACTUAL reconstructed comparison, using the SAME
whole target cover and the transported original frames. No replacement
monoidal comparison or independent-frame invariance is assumed. -/
lemma natural :
    (Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b) ≪≫
      TensorPullbackCocycle318.comparison p U M' N'
        (fun i => em i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso a)
        (fun i => en i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso b) hc=
    TensorPullbackCocycle318.comparison p U M N em en hc ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b) := by
  let em' := fun i => em i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso a
  let en' := fun i => en i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso b
  let E := fun i => LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M N)
    (U i) (TensorLineCocycle318.frames M N U em en i)
  let E' := fun i => LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M' N')
    (U i) (TensorLineCocycle318.frames M' N' U em' en' i)
  let F := TensorLineCocycle318.frames ((Scheme.Modules.pullback p).obj M)
    ((Scheme.Modules.pullback p).obj N) (fun i => p ⁻¹ᵁ U i)
    (fun i => LinePullbackFrames318.frame p M (U i) (em i))
    (fun i => LinePullbackFrames318.frame p N (U i) (en i))
  let F' := TensorLineCocycle318.frames ((Scheme.Modules.pullback p).obj M')
    ((Scheme.Modules.pullback p).obj N') (fun i => p ⁻¹ᵁ U i)
    (fun i => LinePullbackFrames318.frame p M' (U i) (em' i))
    (fun i => LinePullbackFrames318.frame p N' (U i) (en' i))
  have hs (i : ι) : E i ≪≫ (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U i).ι).mapIso
      ((Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b))=E' i := by
    dsimp only [E,E']
    rw [←OriginalChartPullbackFrameNaturality318.frame]
    congr 1
    exact OriginalTensorChartFrameNaturality318.frame a b (U i) (em i) (en i)
  have ht (i : ι) : F i ≪≫ (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U i).ι).mapIso
      (TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b))=F' i := by
    dsimp only [F,F',TensorLineCocycle318.frames]
    rw [OriginalTensorChartFrameNaturality318.frame,
      ←OriginalChartPullbackFrameNaturality318.frame,
      ←OriginalChartPullbackFrameNaturality318.frame]
  apply Iso.ext
  apply OriginalFramedComparisonNormalization318.hom_ext_restrict _
    (fun i => p ⁻¹ᵁ U i) F' (LinePullbackFrames318.preimage_cover p U hc)
  intro i
  apply (cancel_epi (E i).hom).mp
  have hs' := congrArg Iso.hom (hs i)
  have ht' := congrArg Iso.hom (ht i)
  have h0 := congrArg Iso.hom
    (OriginalTensorPullbackFrameNormalization318.frame p U M N em en hc i)
  have h1 := congrArg Iso.hom
    (OriginalTensorPullbackFrameNormalization318.frame p U M' N' em' en' hc i)
  change (E i).hom ≫ _=_ at h0
  change (E' i).hom ≫ _=_ at h1
  simp only [Iso.trans_hom,Functor.mapIso_hom] at hs' ht' h0 h1 ⊢
  rw [Functor.map_comp,Functor.map_comp,←Category.assoc,hs',h1,
    ←Category.assoc,h0,ht']
end OriginalTensorPullbackNaturality318
