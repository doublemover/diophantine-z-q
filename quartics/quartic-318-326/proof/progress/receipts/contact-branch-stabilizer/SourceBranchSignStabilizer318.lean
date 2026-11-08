module
public import SourceSignFieldComparison318
public section
noncomputable section
namespace SourceBranchSignStabilizer318
open ContactKummerOrder318 Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
@[expose] def root (j:Fin 4):SourceOrder c:=FourRootOrderSigns318.generator (coefficient c) j
variable {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
local instance fieldCharZero:CharZero F:=Algebra.charZero_of_charZero ℚ F
variable (p:SourceOrder c→ₐ[R]F) (i:Fin 4)
    (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
lemma scalarPolynomial (q:ℚ):algebraMap R F (C q)=algebraMap ℚ F q:=
  (IsScalarTower.algebraMap_apply ℚ R F q).symm
include ht
lemma root_square (j:Fin 4):p (root c j)^2=
    algebraMap ℚ F (c j:ℚ)*
      (algebraMap ℚ F (LinearContactSquareclass318.contacts i)-
        algebraMap ℚ F (LinearContactSquareclass318.contacts j)):=by
  rw [←map_pow,root,FourRootOrderSigns318.generator_square,AlgHom.commutes,
    coefficient,map_mul,map_sub,scalarPolynomial,ht,scalarPolynomial]
lemma root_zero:p (root c i)=0:=by
  have h:=root_square c p i ht i
  rw [sub_self,mul_zero] at h
  exact sq_eq_zero_iff.mp h
lemma root_ne_zero (j:Fin 4) (hji:j≠i):p (root c j)≠0:=by
  have hc:algebraMap ℚ F (c j:ℚ)≠0:=by
    simpa only [map_zero] using (algebraMap ℚ F).injective.ne (c j).ne_zero
  have ha:algebraMap ℚ F (LinearContactSquareclass318.contacts i)-
      algebraMap ℚ F (LinearContactSquareclass318.contacts j)≠0:=
    sub_ne_zero.mpr ((algebraMap ℚ F).injective.ne
      (LinearContactSquareclass318.contacts_injective.ne hji.symm))
  intro h
  have hs:=root_square c p i ht j
  rw [h,zero_pow (by decide:2≠0)] at hs
  exact mul_ne_zero hc ha hs.symm
/-- At any actual field-valued point above the labelled finite contact,
precisely the corresponding root can be zero. A source sign fixes that
point exactly when all other three signs are false. -/
theorem fixed_iff (b:Fin 4→Bool):
    p.comp (SourceSignFieldComparison318.sourceEquiv c b).toAlgHom=p↔
      ∀j:Fin 4,j≠i→b j=false:=by
  constructor
  · intro he j hji
    have hy:=congrArg (fun f:SourceOrder c→ₐ[R]F=>f (root c j)) he
    change p (FourRootOrderSigns318.signEquiv (coefficient c) b
      (FourRootOrderSigns318.generator (coefficient c) j))=p (root c j) at hy
    rw [FourRootOrderSigns318.signEquiv_generator] at hy
    cases hb:b j
    · rfl
    · simp only [hb,ite_true,map_neg] at hy
      have hz:(2:F)*p (root c j)=0:=by
        change -p (root c j)=p (root c j) at hy
        linear_combination -hy
      exact False.elim ((mul_ne_zero (by norm_num) (root_ne_zero c p i ht j hji)) hz)
  · intro hb
    apply FourRootSignBaseChange318.hom_ext
    intro j
    change p (FourRootOrderSigns318.signEquiv (coefficient c) b
      (FourRootOrderSigns318.generator (coefficient c) j))=p (root c j)
    rw [FourRootOrderSigns318.signEquiv_generator]
    by_cases hji:j=i
    · subst j
      cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_neg]
      · rfl
      · change -p (root c i)=p (root c i)
        rw [root_zero c p i ht,neg_zero]
    · rw [hb j hji]
      rfl
end SourceBranchSignStabilizer318
