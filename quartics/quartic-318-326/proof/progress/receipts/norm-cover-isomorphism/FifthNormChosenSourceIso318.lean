module
public import FifthNormCoverIso318
public import FifthNormSourceIso318
public section
noncomputable section
namespace FifthNormChosenSourceIso318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M N:Model.Modules} (e:M≅N) {α β:Type}
    (A:α→Model.Opens) (B:β→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆i,A i) (hB:(⊤:Model.Opens)≤⨆j,B j)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
/-- Isomorphic original source lines, with independently supplied actual
covering frames, yield genuinely isomorphic constructed norm target lines. -/
@[expose] def iso:
    FifthNormLineObject318.object M A hA eA≅FifthNormLineObject318.object N B hB eB:=
  FifthNormSourceIso318.iso e (FifthLineTargetCover318.neighborhood M A hA eA)
    (FifthLineTargetCover318.frame M A hA eA)
    (LineFrameIsoCocycle318.transported e
      (fun i=>map⁻¹ᵁFifthLineTargetCover318.neighborhood M A hA eA i)
      (FifthLineTargetCover318.frame M A hA eA))≪≫
  FifthNormCoverIso318.iso N
    (FifthLineTargetCover318.neighborhood M A hA eA)
    (FifthLineTargetCover318.neighborhood N B hB eB)
    (LineFrameIsoCocycle318.transported e
      (fun i=>map⁻¹ᵁFifthLineTargetCover318.neighborhood M A hA eA i)
      (FifthLineTargetCover318.frame M A hA eA))
    (FifthLineTargetCover318.frame N B hB eB)
    (FifthLineTargetCover318.cover_top M A hA eA)
    (FifthLineTargetCover318.cover_top N B hB eB)
lemma hom_inv:(iso e A B hA hB eA eB).hom≫(iso e A B hA hB eA eB).inv=𝟙 _:=
  (iso e A B hA hB eA eB).hom_inv_id
lemma inv_hom:(iso e A B hA hB eA eB).inv≫(iso e A B hA hB eA eB).hom=𝟙 _:=
  (iso e A B hA hB eA eB).inv_hom_id
end FifthNormChosenSourceIso318
