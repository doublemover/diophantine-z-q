module
public import OpenClutchedLine318
public import FifthSheafNorm318
public section
noncomputable section
namespace FifthNormClutchedLine318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=FifthOpenNorm318.Model
@[expose] def left:Target.Opens:=FifthChartNorm318.chartOpen false
@[expose] def right:Target.Opens:=FifthChartNorm318.chartOpen true
@[expose] def overlap:Target.Opens:=left⊓right
@[expose] def sourceLeft:Model.Opens:=map⁻¹ᵁleft
@[expose] def sourceRight:Model.Opens:=map⁻¹ᵁright
lemma source_overlap:map⁻¹ᵁoverlap=sourceLeft⊓sourceRight:=map.preimage_inf
lemma target_cover:left⊔right=⊤:=by
  apply le_antisymm le_top
  intro x _
  obtain ⟨b,hb⟩:=FifthTargetNormalBasis318.chart_cover x
  cases b
  · exact Or.inl hb
  · exact Or.inr hb
lemma source_cover:sourceLeft⊔sourceRight=⊤:=by
  rw [sourceLeft,sourceRight,←Scheme.Hom.preimage_sup,target_cover]
  exact map.preimage_top
/-- Transport only by the literal inverse-image/intersection equality. -/
@[expose] def sourceTransition (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    Γ(Model,sourceLeft⊓sourceRight)ˣ:=
  Units.map (Model.presheaf.map (eqToHom source_overlap).op).hom.toMonoidHom a
/-- Exact norm of the original overlap transition unit. -/
@[expose] def targetTransition (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):Γ(Target,overlap)ˣ:=
  FifthOpenNorm318.unitNorm.app (op overlap) a
@[expose] def sourceLine (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):Model.Modules:=
  OpenClutchedLine318.line sourceLeft sourceRight (sourceTransition a)
/-- An actual target line sheaf, not a Picard-group alias. Its transition is
the norm of the specified source transition on this target-pullback cover. -/
@[expose] def normLine (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):Target.Modules:=
  OpenClutchedLine318.line left right (targetTransition a)
@[expose] def sourceFirstFrame (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    (sourceLine a).restrict sourceLeft.ι≅ClutchedModule318.unit sourceLeft.toScheme:=
  OpenClutchedLine318.firstFrame sourceLeft sourceRight (sourceTransition a)
@[expose] def sourceSecondFrame (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    (sourceLine a).restrict sourceRight.ι≅ClutchedModule318.unit sourceRight.toScheme:=
  OpenClutchedLine318.secondFrame sourceLeft sourceRight (sourceTransition a)
@[expose] def firstFrame (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    (normLine a).restrict left.ι≅ClutchedModule318.unit left.toScheme:=
  OpenClutchedLine318.firstFrame left right (targetTransition a)
@[expose] def secondFrame (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    (normLine a).restrict right.ι≅ClutchedModule318.unit right.toScheme:=
  OpenClutchedLine318.secondFrame left right (targetTransition a)
lemma norm_frames_cover (x:Target):(∃y,left.ι y=x)∨(∃y,right.ι y=x):=
  OpenClutchedLine318.frames_cover left right target_cover x
lemma source_frames_cover (x:Model):(∃y,sourceLeft.ι y=x)∨(∃y,sourceRight.ι y=x):=
  OpenClutchedLine318.frames_cover sourceLeft sourceRight source_cover x
lemma target_transition_value (a:Γ(Model,map⁻¹ᵁoverlap)ˣ):
    (targetTransition a).val=FifthOpenNorm318.norm overlap a.val:=rfl
lemma pullback_transition (a:Γ(Target,overlap)ˣ):
    targetTransition (Units.map (map.app overlap).hom.toMonoidHom a)=a^8:=
  FifthOpenNorm318.unit_pullback overlap a
end FifthNormClutchedLine318
