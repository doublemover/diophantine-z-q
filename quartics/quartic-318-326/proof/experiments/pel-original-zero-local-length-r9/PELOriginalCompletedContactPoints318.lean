module
public import PELOriginalContactRootExtensions318
public import FourRootNormalizedPointCharts318
public section
noncomputable section
namespace PELOriginalCompletedContactPoints318
open Set Filter
open scoped Topology OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalBranchLabels318 PELOriginalContactRootExtensions318
open PELOriginalContactParameterLocality318
open FourRootNormalizedPointCharts318

@[expose] def finiteRoots (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) : Fin 4→ℂ→ℂ:=
  (PELOriginalContactRootExtensions318.finite p hp j h).choose
lemma finiteRoots_square (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) (k:Fin 4) :
    finiteRoots p hp j h k 0^2=branches j-branches k := by
  obtain ⟨inv,hA,hG,hS,hrest⟩:=(PELOriginalContactRootExtensions318.finite p hp j h).choose_spec
  exact hS k
lemma finiteRoots_analytic (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) (k:Fin 4) :
    AnalyticAt ℂ (finiteRoots p hp j h k) 0 := by
  obtain ⟨inv,hA,hrest⟩:=(PELOriginalContactRootExtensions318.finite p hp j h).choose_spec
  exact hA k
lemma finiteRoots_agree (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) (k:Fin 4) :
    finiteRoots p hp j h k=ᶠ[𝓝[≠] (0:ℂ)]
      (fun w=>roots (source (finiteParameter p hp j h) w) k) := by
  obtain ⟨inv,hA,hG,hrest⟩:=(PELOriginalContactRootExtensions318.finite p hp j h).choose_spec
  exact hG k
@[expose] def finiteCenter (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) : FinitePoints branches:=
  ⟨(branches j,fun k=>finiteRoots p hp j h k 0),finiteRoots_square p hp j h⟩

@[expose] def infinityUnits (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞) : Fin 4→ℂ→ℂ:=
  (PELOriginalContactRootExtensions318.infinity p hp h).choose
lemma infinityUnits_square (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞) (k:Fin 4) : infinityUnits p hp h k 0^2=1 := by
  obtain ⟨inv,hA,hS,hrest⟩:=(PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact hS k
@[expose] def infinityCenter (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞) : InfinitySigns:=by
  let r:=infinityUnits p hp h
  have hn:r 0 0≠0:=by
    intro hz
    have hh:=infinityUnits_square p hp h 0
    rw [hz,zero_pow (by decide:2≠0)] at hh
    exact zero_ne_one hh
  refine ⟨fun k=>r k 0/r 0 0,div_self hn,?_⟩
  intro k
  rw [div_pow,infinityUnits_square,infinityUnits_square,div_self one_ne_zero]

lemma ramified_of_not_regular (p:UnlevelledBase) (hp:p∉RegularSource) :
    p∈nontrivialStabilizerLocus:=
  (PELStabilizerLocusInvariant318.branch_image_iff p).mp (not_not.mp hp)
lemma not_regular_of_ramified (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus) :
    p∉RegularSource:=fun h=>h ((PELStabilizerLocusInvariant318.branch_image_iff p).mpr hp)

/-- A nonregular finite point lies above one of the four ACTUAL marked
branch values. No cardinality or numeric branch value is substituted. -/
lemma finite_branch (p:UnlevelledBase) (hp:p∉RegularSource) (hn:normalizedMap p≠∞) :
    ∃j:Fin 4,normalizedMap p=(branches j:OnePoint ℂ) := by
  obtain ⟨t,ht⟩:=OnePoint.ne_infty_iff_exists.mp hn
  have hd:FourCharacterRootRecombination318.denominator branches t=0:=by
    by_contra hD
    exact hp (PELOriginalContactRootBranchSource318.regular_of_projection p t ht.symm hD).1
  have hex:∃j:Fin 4,t=branches j:=by
    by_contra hh
    have hne:∀j,t≠branches j:=by simpa using hh
    exact ((FourRootPuncturedRegularity318.denominator_ne_iff branches t).mpr hne) hd
  obtain ⟨j,hj⟩:=hex
  exact ⟨j,ht.symm.trans (congrArg ((↑):ℂ→OnePoint ℂ) hj)⟩
@[expose] def branchIndex (p:UnlevelledBase) (hp:p∉RegularSource) (hn:normalizedMap p≠∞):Fin 4:=
  (finite_branch p hp hn).choose
lemma branchIndex_value (p:UnlevelledBase) (hp:p∉RegularSource) (hn:normalizedMap p≠∞):
    normalizedMap p=(branches (branchIndex p hp hn):OnePoint ℂ):=
  (finite_branch p hp hn).choose_spec

/-- The completed map fills the SAME generic-root map with its actual
analytic extension values. All infinity sign triples are retained. This
is a set map here; continuity and biholomorphy are proved separately. -/
@[expose] def completedMap (p:UnlevelledBase):Completed branches:=
  if hr:p∈RegularSource then
    .inl ⟨(base p,roots p),roots_square p hr⟩
  else if hi:normalizedMap p=∞ then
    .inr (infinityCenter p (ramified_of_not_regular p hr) hi)
  else .inl (finiteCenter p (ramified_of_not_regular p hr)
    (branchIndex p hr hi) (branchIndex_value p hr hi))

lemma completedMap_regular (p:UnlevelledBase) (hp:p∈RegularSource) :
    completedMap p=.inl ⟨(base p,roots p),roots_square p hp⟩:=dif_pos hp
lemma completedMap_infinity (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞) : completedMap p=.inr (infinityCenter p hp h):=by
  rw [completedMap,dif_neg (not_regular_of_ramified p hp),dif_pos h]
lemma completedMap_finiteBranch (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)) :
    completedMap p=.inl (finiteCenter p hp j h) := by
  have hr:=not_regular_of_ramified p hp
  have hn:normalizedMap p≠∞:=by rw [h];exact OnePoint.coe_ne_infty _
  have hj:branchIndex p hr hn=j:=branches_injective
    (OnePoint.coe_injective ((branchIndex_value p hr hn).symm.trans h))
  unfold completedMap
  rw [dif_neg hr,dif_neg hn]
  subst j
  rfl

/-- The whole completed point map preserves the exact original base,
including every finite branch point and each original infinity point. -/
theorem projection_commutes (p:UnlevelledBase) :
    FourRootNormalizedPointCharts318.projection branches (completedMap p)=normalizedMap p := by
  by_cases hr:p∈RegularSource
  · rw [completedMap_regular p hr]
    exact (normalized_finite p hr).symm
  · by_cases hi:normalizedMap p=∞
    · rw [completedMap_infinity p (ramified_of_not_regular p hr) hi]
      exact hi.symm
    · rw [completedMap_finiteBranch p (ramified_of_not_regular p hr)
        (branchIndex p hr hi) (branchIndex_value p hr hi)]
      exact (branchIndex_value p hr hi).symm
end PELOriginalCompletedContactPoints318
