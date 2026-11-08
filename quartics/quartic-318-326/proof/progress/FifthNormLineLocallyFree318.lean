module
public import OpenClutchedLocallyFree318
public import FifthNormClutchedLine318
public section
noncomputable section
namespace FifthNormLineLocallyFree318
open AlgebraicGeometry
open FifthCompletedGlobal318 FifthNormClutchedLine318
variable (a:Γ(Model,map⁻¹ᵁoverlap)ˣ)
/-- Actual source local generator data, with one generator on each entire
inverse-image chart, not just generic rank one. -/
@[expose] def sourceData:(sourceLine a).LocalGeneratorsData:=
  OpenClutchedLocallyFree318.data sourceLeft sourceRight (sourceTransition a) source_cover
@[expose] def normData:(normLine a).LocalGeneratorsData:=
  OpenClutchedLocallyFree318.data left right (targetTransition a) target_cover
lemma sourceData_free:(sourceData a).IsLocallyFreeData:=
  OpenClutchedLocallyFree318.data_free sourceLeft sourceRight (sourceTransition a) source_cover
lemma normData_free:(normData a).IsLocallyFreeData:=
  OpenClutchedLocallyFree318.data_free left right (targetTransition a) target_cover
lemma source_locallyFree:(sourceLine a).IsLocallyFree:=
  OpenClutchedLocallyFree318.locallyFree sourceLeft sourceRight (sourceTransition a) source_cover
lemma norm_locallyFree:(normLine a).IsLocallyFree:=
  OpenClutchedLocallyFree318.locallyFree left right (targetTransition a) target_cover
end FifthNormLineLocallyFree318
