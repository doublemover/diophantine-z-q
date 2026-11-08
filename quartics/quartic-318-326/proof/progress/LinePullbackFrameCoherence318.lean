module
public import PullbackOpenFrameNormalization318
public import OpenFramePullbackRestriction318
public section
noncomputable section
namespace LinePullbackFrameCoherence318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U W:Y.Opens) (h:W≤U)
lemma small_square:
    X.homOfLE (f.preimage_mono h)≫LinePullbackFrames318.chartMap f U=
      LinePullbackFrames318.chartMap f W≫Y.homOfLE h:=by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc,←LinePullbackFrames318.square,←Category.assoc,Scheme.homOfLE_ι,
    Category.assoc,Scheme.homOfLE_ι,←LinePullbackFrames318.square]
/-- The unchanged canonical pulled frame restricts to the canonical pullback
of the unchanged original restricted frame, on the whole inverse-image open. -/
lemma frame (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    OpenLineFrameRefinement318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU)
      (LinePullbackFrames318.frame f M U e) (f⁻¹ᵁW) (f.preimage_mono h)=
    LinePullbackFrames318.frame f M W (OpenLineFrameRefinement318.frame M U e W h):=by
  let j:=U.ι
  let k:=(f⁻¹ᵁU).ι
  let g:=LinePullbackFrames318.chartMap f U
  let m:=X.homOfLE (f.preimage_mono h)
  let l:=Y.homOfLE h
  let q:=LinePullbackFrames318.chartMap f W
  let total:=q≫W.ι
  have hmk:m≫k=(f⁻¹ᵁW).ι:=Scheme.homOfLE_ι X (f.preimage_mono h)
  have hlj:l≫j=W.ι:=Scheme.homOfLE_ι Y h
  have hmg:m≫g=q≫l:=small_square f U W h
  have hmt:m≫(g≫j)=total:=by rw [←Category.assoc,hmg,Category.assoc,hlj]
  have hrj:(q≫l)≫j=total:=by rw [Category.assoc,hlj]
  have hn:=PullbackChartComposition318.nested f j k g (g≫j)
    (LinePullbackFrames318.square f U) rfl m l q (f⁻¹ᵁW).ι W.ι (q≫l) total
    hmk hlj hmg rfl hmt (LinePullbackFrames318.square f W) hrj rfl M
    (e≪≫(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  apply Iso.ext
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback (f⁻¹ᵁW).ι).hom.app
    ((Scheme.Modules.pullback f).obj M))).mp
  change ( _ ≪≫(Scheme.Modules.restrictFunctorIsoPullback (f⁻¹ᵁW).ι).app
    ((Scheme.Modules.pullback f).obj M)).hom=(_≪≫(Scheme.Modules.restrictFunctorIsoPullback
      (f⁻¹ᵁW).ι).app ((Scheme.Modules.pullback f).obj M)).hom
  apply congrArg Iso.hom
  calc
    _=PullbackChartComposition318.extend m k (f⁻¹ᵁW).ι hmk
        ((Scheme.Modules.pullback f).obj M)
        (LinePullbackFrames318.frame f M U e≪≫
          (Scheme.Modules.restrictFunctorIsoPullback k).app ((Scheme.Modules.pullback f).obj M)):=
      OpenFramePullbackRestriction318.normalized _ _ _ _ _
    _=PullbackChartComposition318.extend m k (f⁻¹ᵁW).ι hmk
        ((Scheme.Modules.pullback f).obj M)
        (PullbackChartComposition318.chart f j k g (g≫j)
          (LinePullbackFrames318.square f U) rfl M
          (e≪≫(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)):=
      congrArg (PullbackChartComposition318.extend m k (f⁻¹ᵁW).ι hmk
        ((Scheme.Modules.pullback f).obj M)) (PullbackOpenFrameNormalization318.chart_formula f M U e)
    _=_:=hn
    _=PullbackChartComposition318.chart f W.ι (f⁻¹ᵁW).ι q total
        (LinePullbackFrames318.square f W) rfl M
        (OpenLineFrameRefinement318.frame M U e W h≪≫
          (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M):=
      congrArg (PullbackChartComposition318.chart f W.ι (f⁻¹ᵁW).ι q total
        (LinePullbackFrames318.square f W) rfl M)
        (OpenFramePullbackRestriction318.normalized M U e W h).symm
    _=_:=(PullbackOpenFrameNormalization318.chart_formula f M W
      (OpenLineFrameRefinement318.frame M U e W h)).symm
end LinePullbackFrameCoherence318
