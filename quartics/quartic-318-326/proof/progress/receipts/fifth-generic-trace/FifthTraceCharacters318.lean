module
public import FifthGenericTrace318
public section
noncomputable section
namespace FifthTraceCharacters318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthCompletedFunctionField318
set_option maxHeartbeats 650000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero Raw:=Algebra.charZero_of_charZero (RatFunc ℚ) Raw
local instance characterCharZero:CharZero Character:=Algebra.charZero_of_charZero (RatFunc ℚ) Character
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
/-- A genuine fixing automorphism acts trivially on the relative field trace. -/
lemma invariant (σ:FifthCharacterField318.field.fixingSubgroup) (x:Raw):
    Algebra.trace Character Raw (σ.1 x)=Algebra.trace Character Raw x:=
  Algebra.trace_eq_of_algEquiv (FifthCharacterField318.field.fixingSubgroupEquiv σ) x
/-- Antisymmetry under any actual fixing automorphism forces zero trace. -/
lemma raw_zero_of_anti (σ:FifthCharacterField318.field.fixingSubgroup) (x:Raw)
    (h:σ.1 x= -x):Algebra.trace Character Raw x=0:=by
  have hh:=invariant σ x
  rw [h,map_neg] at hh
  have hz:(2:Character)*Algebra.trace Character Raw x=0:=by linear_combination -hh
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
/-- This criterion concerns the actual generic-stalk trace and its exact
original source-field identification, not a separately assigned field. -/
lemma zero_of_anti (σ:FifthCharacterField318.field.fixingSubgroup)
    (x:Model.functionField) (h:σ.1 (sourceEquiv x)= -sourceEquiv x):
    FifthGenericTrace318.trace x=0:=by
  apply targetEquiv.injective
  rw [FifthGenericTrace318.original_trace,map_zero]
  exact raw_zero_of_anti σ _ h
lemma sign_rat (s:Finset (Fin 4)) (b:Fin 4→Bool):
    CharacterRoot318.sign (F:=RatFunc ℚ) s b=
      algebraMap ℚ (RatFunc ℚ) (∏j∈s,if b j then (-1:ℚ) else 1):=by
  simp only [CharacterRoot318.sign,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases hb:b j <;> simp [hb]
/-- Constructive Boolean character separation by flipping one index inside
and one outside the support.
The empty and full supports are deliberately excluded: they restrict
trivially to this eight-element subgroup. -/
lemma separating_sign:∀s:Finset (Fin 4),s.Nonempty→s≠Finset.univ→
    ∃b:Fin 4→Bool,(∏j:Fin 4,if b j then (-1:ℚ) else 1)=1 ∧
      (∏j∈s,if b j then (-1:ℚ) else 1)= -1:=by
  intro s hs hfull
  obtain ⟨i,hi⟩:=hs
  have hex:∃j:Fin 4,j∉s:=by
    by_contra! h
    exact hfull (Finset.eq_univ_of_forall h)
  obtain ⟨j,hj⟩:=hex
  have hij:i≠j:=by intro h;exact hj (h ▸ hi)
  let b:Fin 4→Bool:=fun k=>decide (k=i ∨ k=j)
  have he:∀k:Fin 4,(if b k then (-1:ℚ) else 1)=
      (if k=i then (-1:ℚ) else 1)*(if k=j then (-1:ℚ) else 1):=by
    intro k
    by_cases hki:k=i
    · subst k
      simp [b,hij]
    · by_cases hkj:k=j <;> simp [b,hki,hkj,hij,Ne.symm hij]
  refine ⟨b,?_,?_⟩
  · simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp
  · simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp [hi,hj]
/-- Every nonempty proper root monomial has zero relative trace, using an
actual even source-sign automorphism that negates that original monomial. -/
lemma root_trace_zero (s:Finset (Fin 4)) (hs:s.Nonempty) (hfull:s≠Finset.univ):
    Algebra.trace Character Raw (CharacterRoot318.root (SourceKummerField318.parameter units) s)=0:=by
  obtain ⟨b,hb,hn⟩:=separating_sign s hs hfull
  have hmem:FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b∈
      FifthCharacterField318.field.fixingSubgroup:=by
    rw [FifthCharacterField318.sign_mem_fixing_iff]
    change CharacterRoot318.sign (F:=RatFunc ℚ) Finset.univ b=1
    rw [sign_rat,hb,map_one]
  apply raw_zero_of_anti ⟨_,hmem⟩
  change FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
    (CharacterRoot318.root (SourceKummerField318.parameter units) s)= -_
  rw [CharacterRoot318.sign_action,sign_rat,hn,map_neg,map_one,map_neg,map_one,neg_one_mul]
/-- The preceding zero is transported through the exact original generic
stalk equivalence, so it is a trace statement about the completed quotient. -/
lemma actual_root_trace_zero (s:Finset (Fin 4)) (hs:s.Nonempty) (hfull:s≠Finset.univ):
    FifthGenericTrace318.trace
      (sourceEquiv.symm (CharacterRoot318.root (SourceKummerField318.parameter units) s))=0:=by
  apply targetEquiv.injective
  rw [FifthGenericTrace318.original_trace,sourceEquiv.apply_symm_apply,map_zero]
  exact root_trace_zero s hs hfull
/-- In particular all four original complementary triple-root characters
have zero trace to the distinct fifth full-root quotient. -/
lemma original_four_trace_zero (i:Fin 4):
    FifthGenericTrace318.trace
      (sourceEquiv.symm (CharacterRoot318.root (SourceKummerField318.parameter units)
        (SourceCharacterFields318.complement i)))=0:=by
  apply actual_root_trace_zero _ (SourceCharacterFields318.complement_nonempty i)
  intro h
  have hi:i∉SourceCharacterFields318.complement i:=by simp [SourceCharacterFields318.complement]
  exact hi (h.symm ▸ Finset.mem_univ i)
end FifthTraceCharacters318
