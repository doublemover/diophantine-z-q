module
public import OriginalPullbackChartVertical318
public import PullbackOpenFrameNormalization318
public section
noncomputable section
namespace OriginalChartFrameCoefficientComposition318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
lemma chartMap :
    LinePullbackFrames318.chartMap f (g ⁻¹ᵁ U) ≫ LinePullbackFrames318.chartMap g U=
      LinePullbackFrames318.chartMap (f ≫ g) U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc,←LinePullbackFrames318.square,←Category.assoc,
    ←LinePullbackFrames318.square,Category.assoc,LinePullbackFrames318.square]
/-- Composition for the exact original full chart frames. The native
coefficient associator and restriction comparison are both retained. -/
lemma frame (M : Z.Modules)
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) :
    LinePullbackFrames318.frame f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
      (LinePullbackFrames318.frame g M U e) ≪≫
      (Scheme.Modules.restrictFunctor ((f ≫ g) ⁻¹ᵁ U).ι).mapIso
        ((Scheme.Modules.pullbackComp f g).app M)=
    LinePullbackFrames318.frame (f ≫ g) M U e := by
  let W := (f ≫ g) ⁻¹ᵁ U
  let R := Scheme.Modules.restrictFunctorIsoPullback W.ι
  let a := (Scheme.Modules.pullbackComp f g).app M
  have hn := R.hom.naturality a.hom
  have hv := OriginalPullbackChartVertical318.chart f g U.ι (g ⁻¹ᵁ U).ι W.ι
    (LinePullbackFrames318.chartMap g U) (LinePullbackFrames318.chartMap f (g ⁻¹ᵁ U))
    (LinePullbackFrames318.square g U) (LinePullbackFrames318.square f (g ⁻¹ᵁ U)) M
    (e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  rw [chartMap] at hv
  apply Iso.ext
  apply (cancel_mono (R.hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M))).mp
  simp only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc]
  rw [hn]
  change ((LinePullbackFrames318.frame f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
      (LinePullbackFrames318.frame g M U e) ≪≫
        R.app ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))) ≪≫
      (Scheme.Modules.pullback W.ι).mapIso a).hom=
    (LinePullbackFrames318.frame (f ≫ g) M U e ≪≫
      R.app ((Scheme.Modules.pullback (f ≫ g)).obj M)).hom
  rw [PullbackOpenFrameNormalization318.chart_formula,
    PullbackOpenFrameNormalization318.chart_formula,PullbackOpenFrameNormalization318.chart_formula]
  exact congrArg Iso.hom hv
end OriginalChartFrameCoefficientComposition318
