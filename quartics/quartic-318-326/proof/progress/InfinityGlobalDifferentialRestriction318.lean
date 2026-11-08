module
public import InfinityDifferentialDivisibility318
public import InfinitySignChart318
public import FifthDifferentialInvariantSummand318
public section
noncomputable section
namespace InfinityGlobalDifferentialRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev I:=InfinityOpenChart318.OpenOrder units
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev j:=InfinityGlobalScheme318.chartEmbedding units
abbrev p:=ContactIntrinsicDifferentials318.structureMap units
abbrev overQ:=InfinityStructureSmooth318.chartEmbedding_over_Q units
/-- The actual restriction of a global intrinsic differential to the whole
infinity affine chart, represented by its unique algebraic differential. -/
@[expose] def form (s:Γ(M,⊤)):KaehlerDifferential ℚ I:=
  (IntrinsicAffineSectionEquiv318.equivalence j p overQ).symm
    (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)
lemma form_restrict (s:Γ(M,⊤)):
    IntrinsicChartSections318.sectionMap j p overQ (form s)=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s:=
  (IntrinsicAffineSectionEquiv318.equivalence j p overQ).apply_symm_apply _
/-- Canonical global pullback restricts through the exact whole infinity
chart/global sign square. No action is inferred from a field alone. -/
theorem form_action (s:Γ(M,⊤)):
    form (ContactDifferentialCharacters318.action (fun _=>true) s)=
      AlgHomDifferential318.map (InfinityDifferentialDivisibility318.sign units) (form s):=by
  let f:=ContactGlobalSigns318.map units (fun _=>true)
  let a:=InfinityDifferentialDivisibility318.sign units
  have hq:j≫f=Spec.map (CommRingCat.ofHom a.toRingHom)≫j:=
    (InfinitySignChart318.actual_square units (fun _=>true)).symm
  have hv:=AffineChartPullbackScalars318.image_le f j j _ hq
  have hn:=DFunLike.congr_fun
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p p
      (ContactDifferentialCharacters318.over_Q (fun _=>true)) a j j overQ overQ hq hv) (form s)
  simp only [AddMonoidHom.comp_apply] at hn
  rw [form_restrict] at hn
  have hr:=IntrinsicDifferentialSectionPullback318.globalSection_restrict f p p
    (ContactDifferentialCharacters318.over_Q (fun _=>true)) (j ''ᵁ ⊤) (j ''ᵁ ⊤) hv s
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p overQ).injective
  rw [form_restrict]
  exact hr.symm.trans hn
/-- Every genuinely invariant global differential has a regular u du
factor on the entire actual infinity chart. -/
theorem fixed_factorization (s:Γ(M,⊤))
    (h:ContactDifferentialCharacters318.action (fun _=>true) s=s):
    ∃a:I,form s=(InfinityOrderCoordinates318.coordinate units*a) •
      KaehlerDifferential.D ℚ I (InfinityOrderCoordinates318.coordinate units):=by
  apply InfinityDifferentialDivisibility318.fixed_factorization
  rw [←form_action,h]
lemma diagonal_mem:(fun _:Fin 4=>true)∈FifthFixingSigns318.signs:=by
  unfold FifthFixingSigns318.signs FifthOpenSigns318.epsilon
  decide +kernel
/-- The previously constructed exact invariant summand satisfies the
actual whole-chart regular divisibility prerequisite for target descent. -/
theorem invariant_factorization (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃a:I,form s=(InfinityOrderCoordinates318.coordinate units*a) •
      KaehlerDifferential.D ℚ I (InfinityOrderCoordinates318.coordinate units):=
  fixed_factorization s (h _ diagonal_mem)
theorem average_factorization (s:Γ(M,⊤)):
    ∃a:I,form (FifthDifferentialAveraging318.average s)=
      (InfinityOrderCoordinates318.coordinate units*a) •
        KaehlerDifferential.D ℚ I (InfinityOrderCoordinates318.coordinate units):=
  invariant_factorization _ (FifthDifferentialInvariantSummand318.average_fixed s)
end InfinityGlobalDifferentialRestriction318
