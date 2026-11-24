module
public import OriginalGlobalCechOverlap318
public import OriginalQuadraticDualizing318
public import Mathlib.LinearAlgebra.Isomorphisms
public section
noncomputable section
namespace OriginalGlobalDualizingClass318
open Polynomial OriginalGlobalP1Residue318 OriginalGlobalCechOverlap318
open OriginalQuadraticDualizing318 OriginalSexticJetMarked318 OriginalGlobalCechRemainder318

variable {E : Type*} [Field E]
abbrev L (E:Type*) [Field E] := LaurentPolynomial E
abbrev Cochains (E:Type*) [Field E] := L E × L E
/-- ξ_V=dv/(2w)=−x ξ_U. For a second coefficient multiplying w the
transition gains a further x⁻³, producing precisely cv (the −x⁻² transition). -/
@[expose] def cvOdd (p:E[X]) : L E :=
  -(aeval (LaurentPolynomial.T (-1)) p * LaurentPolynomial.T 1)
@[simp] theorem odd_add (p q:E[X]) : cvOdd (p+q)=cvOdd p+cvOdd q := by
  simp only [cvOdd,map_add,add_mul,neg_add]
@[simp] theorem odd_zero : cvOdd (0:E[X])=0 := by simp [cvOdd]
theorem odd_mono (n:ℕ) (a:E) : cvOdd (monomial n a)=mon (-a) (1-(n:ℤ)) := by
  rw [cvOdd,← C_mul_X_pow_eq_monomial,map_mul,aeval_C,aeval_X_pow,LaurentPolynomial.T_pow,
    LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply,LaurentPolynomial.mul_T_assoc,
    mon,map_neg,neg_mul]
  congr 3
  omega

theorem odd_exact (h:L E) : ∃ p q:E[X], h=cu p+cvOdd q := by
  induction h using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨p,q,hp⟩:=ha
    obtain ⟨u,v,hu⟩:=hb
    exact ⟨p+u,q+v,by rw [cu_add,odd_add]; linear_combination hp+hu⟩
  | C_mul_T n a =>
    change ∃ p q:E[X], mon a n=cu p+cvOdd q
    by_cases hn : 0≤n
    · refine ⟨monomial n.toNat a,0,?_⟩
      simp [Int.toNat_of_nonneg hn]
    · refine ⟨0,monomial (1-n).toNat (-a),?_⟩
      have hi : 0≤1-n := by omega
      simp only [cu_zero,odd_mono,neg_neg,Int.toNat_of_nonneg hi,zero_add]
      congr 1
      omega

@[expose] def restriction (d:(E[X]×E[X])×(E[X]×E[X])) : Cochains E :=
  (cu d.1.1+cvOdd d.2.1, cu d.1.2+cv d.2.2)
@[expose] def boundaries (E:Type*) [Field E] : Submodule E (Cochains E) :=
  Submodule.span E (Set.range restriction)

@[expose] def traceRes (E:Type*) [Field E] : Cochains E→ₗ[E]E where
  toFun a:=res a.2
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem exact (E:Type*) [Field E] : boundaries E=(traceRes E).ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr; rintro w ⟨d,rfl⟩
    change res (cu d.1.2+cv d.2.2)=0
    rw [res_add,(chart_zero _).1,(chart_zero _).2,add_zero]
  · rintro ⟨a,b⟩ hb
    obtain ⟨p,q,hp⟩:=odd_exact a
    obtain ⟨u,v,hv⟩:=(exact_cech b).mp hb
    apply Submodule.subset_span
    exact ⟨((p,u),(q,v)),Prod.ext hp.symm hv.symm⟩

theorem onto (E:Type*) [Field E] : Function.Surjective (traceRes E) := by
  intro a; refine ⟨(0,mon a (-1)),?_⟩
  change res (mon a (-1))=a
  simp [res_mon]
/-- The unnormalized dualizing Čech trace is an isomorphism on its actual
two-affine cohomology quotient. Its normalization comes from finite evaluation
at 1 followed by the standard projective-line Laurent residue. -/
@[expose] def traceClass (E:Type*) [Field E] : (Cochains E ⧸ boundaries E) ≃ₗ[E] E :=
  (Submodule.quotEquivOfEq _ _ (exact E)).trans ((traceRes E).quotKerEquivOfSurjective (onto E))
theorem trace_mk (d:Cochains E) : traceClass E (Submodule.Quotient.mk d)=res d.2 := rfl

variable {K:Type*} [Field K] [Algebra E K]
/-- On the true quadratic overlap, the Laurent pullback form h dx has
coordinates (0,2h) in the regular frame dx/(2y). -/
@[expose] def actual (J:Certificate E K) (k:Fin 3) : Cochains E ⧸ boundaries E :=
  Submodule.Quotient.mk (0,2*form J k)
theorem counit (J:Certificate E K) (k:Fin 3) :
    traceClass E (actual J k)=moment J k := by
  rw [actual,trace_mk]
  change res (2*form J k)=_
  rw [two_mul,res_add,residue]
  unfold moment coef; ring

theorem overlap_trace (f h:L E) :
    toDual f (h • (2*y f)) 1 = 2*h := by
  rw [push_pull,Algebra.trace_algebraMap_of_basis (basis f),Fintype.card_fin]
  simp

end OriginalGlobalDualizingClass318
#print axioms OriginalGlobalDualizingClass318.traceClass
#print axioms OriginalGlobalDualizingClass318.counit
