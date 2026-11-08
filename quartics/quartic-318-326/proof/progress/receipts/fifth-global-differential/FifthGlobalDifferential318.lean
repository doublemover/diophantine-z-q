module
public import FifthFormFullCompatibility318
public import ContactGlobalBicanonical318
public section
noncomputable section
namespace FifthGlobalDifferential318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev opens:=ContactGlobalBicanonical318.opens units
@[expose] def localForm:(i:Option (Fin 4))→Γ(M,opens i)
  | some i=>FifthFormLocalSections318.branch i
  | none=>FifthFormLocalSections318.infinity

theorem compatible:TopCat.Presheaf.IsCompatible M.presheaf opens localForm:=by
  intro i j
  cases i with
  | none=>
    cases j with
    | none=>rfl
    | some j=>exact LocalSectionCompatibility318.symm _ _ _ _ _ (FifthFormFullCompatibility318.branch_infinity j)
  | some i=>
    cases j with
    | none=>exact FifthFormFullCompatibility318.branch_infinity i
    | some j=>
      by_cases hij:i=j
      · subst j;rfl
      · exact FifthFormFullCompatibility318.finite_pair i j hij

/-- A genuine fifth global regular intrinsic differential on the actual
complete contact normalization. Its full-root normalization is fixed on the
whole unbranched chart; it is not yet identified with a completed quotient pullback. -/
@[expose] def differential:Γ(M,⊤):=
  ModuleGlobalSections318.gluedTop M opens (ContactGlobalBicanonical318.cover units)
    localForm compatible

theorem restrict (i:Option (Fin 4)):
    M.presheaf.map (homOfLE (show opens i≤⊤ from le_top)).op differential=localForm i:=
  ModuleGlobalSections318.gluedTop_restrict M opens (ContactGlobalBicanonical318.cover units)
    localForm compatible i

theorem common_restrict (j:Fin 4):M.presheaf.map (homOfLE (show
    ContactOverlapIntrinsic318.embedding units ''ᵁ ⊤≤⊤ from le_top)).op differential=
      FifthFormCommonOpen318.branch j:=by
  have h:=congrArg (M.presheaf.map
    (homOfLE (ContactFiniteTensorRestrictions318.branchLE units j)).op) (restrict (some j))
  exact (CategoryTheory.Functor.map_comp_apply M.presheaf
    (homOfLE (show opens (some j)≤⊤ from le_top)).op
    (homOfLE (ContactFiniteTensorRestrictions318.branchLE units j)).op differential).trans
    (h.trans (FifthFormLocalSections318.branch_restrict j))
end FifthGlobalDifferential318
