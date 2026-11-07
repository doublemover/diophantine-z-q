module
public import AdicEvaluation318
public import Mathlib.RingTheory.AdicCompletion.Topology
public import ContactBaseChange318
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public section
noncomputable section
namespace CompleteContactEvaluation318
set_option maxHeartbeats 600000
open PowerSeries
open scoped TensorProduct
variable {A R:Type*} [CommRing A] [CommRing R]

/-- Actual evaluation into an algebraically complete separated adic ring;
the topology and its completeness are derived, not extra input fields. -/
@[expose] def completeEval (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (x:R) (hx:x∈I) : A⟦X⟧→+*R := by
  letI : WithIdeal R:=⟨I⟩
  have ht:CompleteSpace R ∧ T2Space R:=
    (IsAdic.isAdicComplete_iff (R:=R) (I:=I) (by rfl)).mp hc
  letI:=ht.1
  letI:=ht.2
  exact AdicEvaluation318.eval f x hx

@[simp] theorem completeEval_C (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (x:R) (hx:x∈I) (a:A) : completeEval I hc f x hx (C a)=f a := by
  letI : WithIdeal R:=⟨I⟩
  have ht:CompleteSpace R ∧ T2Space R:=
    (IsAdic.isAdicComplete_iff (R:=R) (I:=I) (by rfl)).mp hc
  letI:=ht.1
  letI:=ht.2
  exact AdicEvaluation318.eval_C f x hx a

@[simp] theorem completeEval_X (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (x:R) (hx:x∈I) : completeEval I hc f x hx X=x := by
  letI : WithIdeal R:=⟨I⟩
  have ht:CompleteSpace R ∧ T2Space R:=
    (IsAdic.isAdicComplete_iff (R:=R) (I:=I) (by rfl)).mp hc
  letI:=ht.1
  letI:=ht.2
  exact AdicEvaluation318.eval_X f x hx

theorem contact_mem (I:Ideal R) (u:Rˣ) (pi:R) (m:ℕ) (hp:pi∈I) (hm:0<m) :
    (u:R)*pi^(2*m)∈I := by
  apply I.mul_mem_left
  apply I.pow_mem_of_mem hp
  omega

/-- Positive even contact gives a concrete formal base map, allowing mixed characteristic. -/
@[expose] def contactEval (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:pi∈I) (hm:0<m) : A⟦X⟧→+*R :=
  completeEval I hc f ((u:R)*pi^(2*m)) (contact_mem I u pi m hp hm)

@[simp] theorem contactEval_X (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:pi∈I) (hm:0<m) :
    contactEval I hc f u pi m hp hm X=(u:R)*pi^(2*m) :=
  completeEval_X I hc f _ _

@[simp] theorem contactEval_C (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:pi∈I) (hm:0<m) (a:A) :
    contactEval I hc f u pi m hp hm (C a)=f a :=
  completeEval_C I hc f _ _ a

/-- Actual formal-cover base change with the formal parameter map constructed
from completeness, rather than supplied as a ring-homomorphism hypothesis. -/
@[expose] def actualFormalBaseChange [IsDomain A]
    (I:Ideal R) (hc:IsAdicComplete I R) (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:pi∈I) (hm:0<m) :
    letI:Algebra A⟦X⟧ R:=(contactEval I hc f u pi m hp hm).toAlgebra
    R ⊗[A⟦X⟧] RingQuadraticBasis318.Cover A ≃ₐ[R]
      QuadraticPresentation318.RootRing ((u:R)*pi^(2*m)) := by
  letI:Algebra A⟦X⟧ R:=(contactEval I hc f u pi m hp hm).toAlgebra
  exact ContactBaseChange318.formalBaseChange A u pi m (contactEval_X I hc f u pi m hp hm)

/-- Exact complete-DVR specialization: an irreducible uniformizer supplies
maximal-ideal membership, and both the constant and contact values are proved. -/
theorem complete_dvr_map [IsDomain R] [IsDiscreteValuationRing R]
    (hc:IsAdicComplete (IsLocalRing.maximalIdeal R) R) (f:A→+*R)
    (u:Rˣ) (pi:R) (m:ℕ) (hp:Irreducible pi) (hm:0<m) :
    ∃e:A⟦X⟧→+*R, e X=(u:R)*pi^(2*m) ∧ ∀a:A,e (C a)=f a := by
  have hpi:pi∈IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff] using hp.not_isUnit
  exact ⟨contactEval _ hc f u pi m hpi hm,contactEval_X _ hc f u pi m hpi hm,
    contactEval_C _ hc f u pi m hpi hm⟩

end CompleteContactEvaluation318
