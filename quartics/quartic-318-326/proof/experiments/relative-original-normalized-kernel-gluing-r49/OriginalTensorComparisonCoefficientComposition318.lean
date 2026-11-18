module
public import OriginalChartFrameCoefficientComposition318
public section
noncomputable section
namespace OriginalTensorComparisonCoefficientComposition318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {ι : Type u}
  (U : ι → Z.Opens) (M N : Z.Modules)
  (em : ∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:Z.Opens)≤⨆i,U i)
/-- Exact coefficient-composition square of the original reconstructed
tensor comparisons, using the native module pullback associators. All
three maps are the old maps, normalized on the whole original cover. -/
lemma composition :
    (Scheme.Modules.pullback f).mapIso (TensorPullbackCocycle318.comparison g U M N em en hc) ≪≫
      TensorPullbackCocycle318.comparison f (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (fun i => LinePullbackFrames318.frame g M (U i) (em i))
        (fun i => LinePullbackFrames318.frame g N (U i) (en i))
        (LinePullbackFrames318.preimage_cover g U hc) ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app M)
        ((Scheme.Modules.pullbackComp f g).app N)=
    (Scheme.Modules.pullbackComp f g).app (IntrinsicTensorSheaf318.tensor M N) ≪≫
      TensorPullbackCocycle318.comparison (f ≫ g) U M N em en hc := by
  let V := fun i => g ⁻¹ᵁ U i
  let W := fun i => (f ≫ g) ⁻¹ᵁ U i
  let gm := fun i => LinePullbackFrames318.frame g M (U i) (em i)
  let gn := fun i => LinePullbackFrames318.frame g N (U i) (en i)
  let Cg := TensorPullbackCocycle318.comparison g U M N em en hc
  let Cf := TensorPullbackCocycle318.comparison f V ((Scheme.Modules.pullback g).obj M)
    ((Scheme.Modules.pullback g).obj N) gm gn (LinePullbackFrames318.preimage_cover g U hc)
  let Cfg := TensorPullbackCocycle318.comparison (f ≫ g) U M N em en hc
  let A := TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app M)
    ((Scheme.Modules.pullbackComp f g).app N)
  let E := fun i => LinePullbackFrames318.frame f
    ((Scheme.Modules.pullback g).obj (IntrinsicTensorSheaf318.tensor M N)) (V i)
    (LinePullbackFrames318.frame g (IntrinsicTensorSheaf318.tensor M N) (U i)
      (TensorLineCocycle318.frames M N U em en i))
  let F := fun i => TensorLineLocalFrame318.frame ((Scheme.Modules.pullback (f ≫ g)).obj M)
    ((Scheme.Modules.pullback (f ≫ g)).obj N) (W i)
    (LinePullbackFrames318.frame (f ≫ g) M (U i) (em i))
    (LinePullbackFrames318.frame (f ≫ g) N (U i) (en i))
  have hleft (i : ι) : E i ≪≫ (Scheme.Modules.restrictFunctor (W i).ι).mapIso
      ((Scheme.Modules.pullback f).mapIso Cg ≪≫ Cf ≪≫ A)=F i := by
    have h0 : E i ≪≫ (Scheme.Modules.restrictFunctor (W i).ι).mapIso
        ((Scheme.Modules.pullback f).mapIso Cg)=
      LinePullbackFrames318.frame f (IntrinsicTensorSheaf318.tensor
        ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)) (V i)
        (TensorLineCocycle318.frames ((Scheme.Modules.pullback g).obj M)
          ((Scheme.Modules.pullback g).obj N) V gm gn i) := by
      dsimp only [E]
      rw [←OriginalChartPullbackFrameNaturality318.frame,
        OriginalTensorPullbackFrameNormalization318.frame]
    have h1 := OriginalTensorPullbackFrameNormalization318.frame f V
      ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) gm gn
      (LinePullbackFrames318.preimage_cover g U hc) i
    have h2 : TensorLineCocycle318.frames
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) W
        (fun i => LinePullbackFrames318.frame f ((Scheme.Modules.pullback g).obj M) (V i) (gm i))
        (fun i => LinePullbackFrames318.frame f ((Scheme.Modules.pullback g).obj N) (V i) (gn i)) i ≪≫
        (Scheme.Modules.restrictFunctor (W i).ι).mapIso A=F i := by
      dsimp only [TensorLineCocycle318.frames,A,F,gm,gn]
      rw [OriginalTensorChartFrameNaturality318.frame,
        OriginalChartFrameCoefficientComposition318.frame,
        OriginalChartFrameCoefficientComposition318.frame]
    apply Iso.ext
    have hh0 := congrArg Iso.hom h0
    have hh1 := congrArg Iso.hom h1
    have hh2 := congrArg Iso.hom h2
    simp only [Iso.trans_hom,Functor.mapIso_hom] at hh0 hh1 hh2 ⊢
    rw [Functor.map_comp,Functor.map_comp,←Category.assoc,hh0,←Category.assoc,hh1,hh2]
  have hright (i : ι) : E i ≪≫ (Scheme.Modules.restrictFunctor (W i).ι).mapIso
      ((Scheme.Modules.pullbackComp f g).app (IntrinsicTensorSheaf318.tensor M N) ≪≫ Cfg)=F i := by
    have h0 := OriginalChartFrameCoefficientComposition318.frame f g (U i)
      (IntrinsicTensorSheaf318.tensor M N) (TensorLineCocycle318.frames M N U em en i)
    have h1 := OriginalTensorPullbackFrameNormalization318.frame (f ≫ g) U M N em en hc i
    apply Iso.ext
    have hh0 := congrArg Iso.hom h0
    have hh1 := congrArg Iso.hom h1
    simp only [Iso.trans_hom,Functor.mapIso_hom] at hh0 hh1 ⊢
    rw [Functor.map_comp,←Category.assoc,hh0]
    exact hh1
  apply Iso.ext
  apply OriginalFramedComparisonNormalization318.hom_ext_restrict _ W F
    (LinePullbackFrames318.preimage_cover (f ≫ g) U hc)
  intro i
  apply (cancel_epi (E i).hom).mp
  exact (congrArg Iso.hom (hleft i)).trans (congrArg Iso.hom (hright i)).symm
end OriginalTensorComparisonCoefficientComposition318
