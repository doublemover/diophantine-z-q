module
public import NormalizedLegendreProjectiveModel318
public import CompletedFieldPoints318
public section
noncomputable section
namespace NormalizedLegendreFieldPoints318
open NormalizedLegendreProjectiveModel318
set_option maxHeartbeats 600000

/-- Literal Legendre coordinates, before translation to the actual short
Weierstrass chart. This parameter is the constructed fourth branch value. -/
@[expose] def FinitePoints (l:ℂ) :=
  {p:ℂ×ℂ // p.2^2=p.1*(p.1-1)*(p.1-l)}

/-- Translation is performed on the same finite points, not on an
unrelated model carrying a convenient equation. -/
@[expose] def translated (l:ℂ) : FinitePoints l ≃
    AffineEquationFunctor318.Solutions (S:=ℂ) (A l) (B l) where
  toFun p:=⟨(p.val.1-shift l,p.val.2),by
    change p.val.2^2-(p.val.1-shift l)^3-A l*(p.val.1-shift l)-B l=0
    have ht:=translated_polynomial l p.val.1
    linear_combination p.property-ht⟩
  invFun p:=⟨(p.val.1+shift l,p.val.2),by
    have hp:=p.property
    change p.val.2^2-p.val.1^3-A l*p.val.1-B l=0 at hp
    have ht:=translated_polynomial l (p.val.1+shift l)
    rw [add_sub_cancel_right] at ht
    linear_combination hp+ht⟩
  left_inv p:=by
    apply Subtype.ext
    exact Prod.ext (sub_add_cancel _ _) rfl
  right_inv p:=by
    apply Subtype.ext
    exact Prod.ext (add_sub_cancel_right _ _) rfl

@[expose] def finiteScheme (l:ℂ) : FinitePoints l ≃
    AffineSchemeSolutions318.SchemePoints (K:=ℂ) (A l) (B l):=
  (translated l).trans (AffineSchemeSolutions318.schemeSolutionEquiv (A l) (B l)).symm

/-- Complete original Scheme-valued complex points, including its actual
infinity section. The equivalence is obtained from the two Scheme charts,
not a topology or complex structure transported from the source cover. -/
@[expose] def schemeEquiv (l:ℂ) : Option (FinitePoints l) ≃
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A l) (B l):=
  (Equiv.optionCongr (finiteScheme l)).trans
    (CompletedFieldPoints318.completedEquiv (K:=ℂ) (A l) (B l)).symm

lemma scheme_none (l:ℂ) : schemeEquiv l none=
    CompletedFieldPoints318.infinityPoint (A l) (B l):=rfl
lemma scheme_some (l:ℂ) (p:FinitePoints l) : schemeEquiv l (some p)=
    CompletedFieldPoints318.finiteInclusion (A l) (B l) (finiteScheme l p):=rfl

/-- The deck sign is the actual y-coordinate sign in the original
Legendre equation; its fixed points are exactly the three finite roots. -/
@[expose] def sign (l:ℂ) : FinitePoints l ≃ FinitePoints l where
  toFun p:=⟨(p.val.1,-p.val.2),by simpa only [neg_sq] using p.property⟩
  invFun p:=⟨(p.val.1,-p.val.2),by simpa only [neg_sq] using p.property⟩
  left_inv p:=by apply Subtype.ext; simp
  right_inv p:=by apply Subtype.ext; simp

lemma sign_fixed_iff (l:ℂ) (p:FinitePoints l) : sign l p=p ↔ p.val.2=0 := by
  constructor
  · intro h
    have hh:=congrArg (fun q:FinitePoints l=>q.val.2) h
    change -p.val.2=p.val.2 at hh
    linear_combination hh
  · intro h
    apply Subtype.ext
    exact Prod.ext rfl (by simpa only [h,neg_zero])

lemma zero_iff_branch (l:ℂ) (p:FinitePoints l) :
    p.val.2=0 ↔ p.val.1=0 ∨ p.val.1=1 ∨ p.val.1=l := by
  have hz : p.val.2^2=0 ↔ p.val.1=0 ∨ p.val.1=1 ∨ p.val.1=l := by
    rw [p.property]
    simp only [mul_eq_zero,sub_eq_zero]
    tauto
  simpa only [pow_eq_zero_iff (by decide : 2≠0)] using hz

/-- The original finite fiber has no identifications other than the
actual sign. This is an equality of literal coordinates, not cardinality
used as a substitute for a map. -/
theorem same_coordinate (l:ℂ) (p q:FinitePoints l) :
    p.val.1=q.val.1 ↔ p=q ∨ sign l p=q := by
  constructor
  · intro hx
    have hs : (p.val.2-q.val.2)*(p.val.2+q.val.2)=0 := by
      have hp:=p.property
      have hq:=q.property
      rw [hx] at hp
      linear_combination hp-hq
    rcases mul_eq_zero.mp hs with hs|hs
    · left
      apply Subtype.ext
      exact Prod.ext hx (sub_eq_zero.mp hs)
    · right
      apply Subtype.ext
      refine Prod.ext hx ?_
      change -p.val.2=q.val.2
      linear_combination -hs
  · rintro (rfl|h)
    · rfl
    · exact congrArg (fun r:FinitePoints l=>r.val.1) h
end NormalizedLegendreFieldPoints318
