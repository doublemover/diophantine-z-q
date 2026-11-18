module
public import FourRootCompletedSchemePoints318
public import PELOriginalCompletedContactBiholomorph318
public section
noncomputable section
namespace PELOriginalContactSchemePoints318
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318
open FourRootNormalizedPointCharts318 FourRootCompletedSchemePoints318

/-- The whole ORIGINAL contact source gives exactly the base-preserving
complex-valued points of the independently glued algebraic four-root
Scheme. This is an exact point comparison, NOT an assertion that an
analytic map has already been algebraized as a Scheme morphism. -/
@[expose] def comparison:UnlevelledBase≃SchemePoints branches:=
  PELOriginalCompletedContactBiholomorph318.comparison.toEquiv.trans
    (schemePointEquiv branches)
lemma comparison_value (p:UnlevelledBase):
    comparison p=completedPoint branches (completedMap p):=rfl
lemma finite_value {p:UnlevelledBase} {q:FinitePoints branches}
    (h:completedMap p=.inl q):comparison p=finitePoint branches q:=by
  rw [comparison_value,h];rfl
lemma infinity_value {p:UnlevelledBase} {s:InfinitySigns}
    (h:completedMap p=.inr s):comparison p=infinityPoint branches (center branches s):=by
  rw [comparison_value,h];rfl
/-- No additional algebraic points are silently excluded from the
comparison; all Scheme-valued complex points have one original source. -/
theorem exact_source (q:SchemePoints branches):∃!p:UnlevelledBase,comparison p=q:=by
  refine ⟨comparison.symm q,comparison.apply_symm_apply q,?_⟩
  intro p hp
  exact comparison.injective (hp.trans (comparison.apply_symm_apply q).symm)
end PELOriginalContactSchemePoints318
