module
public import FifthDifferentialAveraging318
public section
noncomputable section
namespace ContactGlobalDifferentialCoefficient318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthSignRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev L:=FifthCharacterField318.L
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
/-- The unique algebraic differential representing the restriction of any
actual global intrinsic differential to the entire unbranched chart. -/
@[expose] def form:Γ(M,⊤)→+KaehlerDifferential ℚ O where
  toFun s:=(IntrinsicAffineSectionEquiv318.equivalence j p (ContactOverlapIntrinsic318.over_Q units)).symm
    (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)
  map_zero':=by simp
  map_add':=by intros; simp
lemma form_restrict (s:Γ(M,⊤)):
    IntrinsicChartSections318.sectionMap j p (ContactOverlapIntrinsic318.over_Q units) (form s)=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s:=
  (IntrinsicAffineSectionEquiv318.equivalence j p (ContactOverlapIntrinsic318.over_Q units)).apply_symm_apply _
/-- The dt coefficient in the original full contact field. The coefficient
is obtained from a genuine section through the actual whole-open frame. -/
@[expose] def coefficient:Γ(M,⊤)→+L:=
  (SourceOpenFractionField318.openEmbedding units).toAddMonoidHom.comp
    ((ContactUnbranchedDifferentialFrame318.frame units).toAddEquiv.toAddMonoidHom.comp form)
lemma coefficient_apply (s:Γ(M,⊤)):coefficient s=
    SourceOpenFractionField318.openEmbedding units
      (ContactUnbranchedDifferentialFrame318.frame units (form s)):=rfl
lemma form_action (b:Fin 4→Bool) (s:Γ(M,⊤)):
    form (ContactDifferentialCharacters318.action b s)=
      AlgHomDifferential318.map (FifthOpenSigns318.sign b) (form s):=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p
    (ContactOverlapIntrinsic318.over_Q units)).injective
  rw [form_restrict]
  exact FifthSignRestriction318.restrict_action b s (form s) (form_restrict s)
/-- Naturality in the real dt frame, including the exact original field
embedding, for every actual global differential section. -/
theorem coefficient_action (b:Fin 4→Bool) (s:Γ(M,⊤)):
    coefficient (ContactDifferentialCharacters318.action b s)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b (coefficient s):=by
  simp only [coefficient_apply,form_action]
  exact FifthOpenSigns318.raw_pullback b (form s)
theorem coefficient_signSum (s:Γ(M,⊤)):
    coefficient (FifthDifferentialAveraging318.signSum s)=
      ∑b∈FifthFixingSigns318.signs,
        FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b (coefficient s):=by
  rw [FifthDifferentialAveraging318.signSum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact coefficient_action b s
end ContactGlobalDifferentialCoefficient318
