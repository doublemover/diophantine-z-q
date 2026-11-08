module
public import LineFrameIsoCocycle318
public import FifthNormGaugeIso318
public section
noncomputable section
namespace FifthNormSourceIso318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M N:Model.Modules} (e:M≅N) {ι:Type} (U:ι→Target.Opens)
    (frames:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
    (newFrames:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (map⁻¹ᵁU i).ι)
abbrev transported:=LineFrameIsoCocycle318.transported e (fun i=>map⁻¹ᵁU i) frames
/-- The actual target norm-cocycle is unchanged by exact transport of source
frames through the supplied original module-sheaf isomorphism. -/
lemma norm_cocycle_eq:
    FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map N U (transported e U frames))=
      FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map M U frames):=
  congrArg FifthNormCocycle318.transfer (LineFrameIsoCocycle318.inverseImage_eq e map U frames)
/-- Actual source-line-isomorphism compatibility of the normed target objects
on a specified common complete inverse-image cover. -/
@[expose] def iso:
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M U frames))≅
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map N U newFrames)):=
  eqToIso (congrArg (CocycleModule318.object U) (norm_cocycle_eq e U frames).symm)≪≫
    FifthNormGaugeIso318.ofOriginalFrames U N (transported e U frames) newFrames
lemma hom_inv:(iso e U frames newFrames).hom≫(iso e U frames newFrames).inv=𝟙 _:=
  (iso e U frames newFrames).hom_inv_id
lemma inv_hom:(iso e U frames newFrames).inv≫(iso e U frames newFrames).hom=𝟙 _:=
  (iso e U frames newFrames).inv_hom_id
end FifthNormSourceIso318
