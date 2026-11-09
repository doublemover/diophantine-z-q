module
public import OpenChartModuleImages318
public import LocalLineGlobalFrames318
public section
noncomputable section
namespace OpenChartLineEffectivity318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (L : ∀ i, LineSheafClass318.Line (U i).toScheme)
  (D : OpenSheafTransition318.Data U
    (OpenChartModuleImages318.ambient U (fun i => (L i).object)))

/-- Glue arbitrary original local line sheaves, not only chartwise
trivial lines. Their own full frame families are refined to actual ambient
open images and retained in the resulting global line. -/
@[expose] def line (hcover : (⊤ : X.Opens) ≤ iSup U) : LineSheafClass318.Line X :=
  LocalLineGlobalFrames318.line U L
    (OpenChartModuleImages318.glued U (fun i => (L i).object) D)
    (OpenChartModuleImages318.comparison U (fun i => (L i).object) D) hcover

/-- The global line recovers the unchanged original local line object on
every original chart through the same explicit gluing/direct-image comparison. -/
@[expose] def comparison (hcover : (⊤ : X.Opens) ≤ iSup U) (i : ι) :
    (line U L D hcover).object.restrict (U i).ι ≅ (L i).object :=
  OpenChartModuleImages318.comparison U (fun i => (L i).object) D i

include D in
/-- Open-cover effectivity for original local lines with genuine coherent
ambient sheaf transitions. Converted scheme-local triple coherence remains
an explicit further bridge, not an added hidden equality here. -/
theorem effective (hcover : (⊤ : X.Opens) ≤ iSup U) :
    ∃ (K : LineSheafClass318.Line X), ∀ i, Nonempty (K.object.restrict (U i).ι ≅ (L i).object) :=
  ⟨line U L D hcover, fun i => ⟨comparison U L D hcover i⟩⟩
end OpenChartLineEffectivity318
