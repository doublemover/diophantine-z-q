module
public import FifthAffineCharacter318
public import FifthActualDifferentialRestriction318
public section
noncomputable section
namespace FifthSignRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthOpenSigns318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev j:=ContactOverlapIntrinsic318.embedding units
abbrev p:=ContactIntrinsicDifferentials318.structureMap units
/-- Canonical whole-Scheme source-sign pullback restricts through the actual
entire common-open square, for any genuine global differential section. -/
theorem restrict_action (b:Fin 4→Bool) (s:Γ(M,⊤)) (ω:KaehlerDifferential ℚ O)
    (hs:IntrinsicChartSections318.sectionMap j p (ContactOverlapIntrinsic318.over_Q units) ω=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s):
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (ContactDifferentialCharacters318.action b s)=
    IntrinsicChartSections318.sectionMap j p (ContactOverlapIntrinsic318.over_Q units)
      (AlgHomDifferential318.map (sign b) ω):=by
  let f:=ContactGlobalSigns318.map units b
  have hq:j≫f=Spec.map (CommRingCat.ofHom (sign b).toRingHom)≫j:=
    ContactGlobalSigns318.on_open units b
  have hv:=AffineChartPullbackScalars318.image_le f j j _ hq
  have hn:=DFunLike.congr_fun
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p p
      (ContactDifferentialCharacters318.over_Q b) (sign b) j j
      (ContactOverlapIntrinsic318.over_Q units) (ContactOverlapIntrinsic318.over_Q units) hq hv) ω
  simp only [AddMonoidHom.comp_apply] at hn
  rw [hs] at hn
  have hr:=IntrinsicDifferentialSectionPullback318.globalSection_restrict f p p
    (ContactDifferentialCharacters318.over_Q b) (j ''ᵁ ⊤) (j ''ᵁ ⊤) hv s
  exact hr.symm.trans hn
end FifthSignRestriction318
