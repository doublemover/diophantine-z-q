module
public import PELOriginalCM210BoundedIdealFactors318
public import PELOriginalCM210BoundedClassRepresentatives318
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public section
noncomputable section
namespace PELOriginalCM210NativeClassGeneration318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210FourNativePrimes318
open PELOriginalCM210NativePrimeClasses318 PELOriginalCM210BoundedMaximalIdeals318
open PELOriginalCM210BoundedIdealFactors318
open scoped nonZeroDivisors
lemma bounded_class_mem (S:Subgroup (ClassGroup O))
    (hS:∀i:Fin 4,primeClass i∈S) (I:Ideal O) :
    ∀(hI:I∈(Ideal O)⁰),Ideal.absNorm I≤18→ClassGroup.mk0 ⟨I,hI⟩∈S := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro hI _
    exact False.elim ((mem_nonZeroDivisors_iff_ne_zero.mp hI) rfl)
  | h₂ I hunit =>
    have htop : I=⊤ := by simpa using hunit
    subst I
    intro hI _
    simpa using S.one_mem
  | h₃ I P hI hP ih =>
    intro hPI hn
    have hInz : I∈(Ideal O)⁰ := mem_nonZeroDivisors_of_ne_zero hI
    have hPnz : P∈(Ideal O)⁰ := mem_nonZeroDivisors_of_ne_zero hP.ne_zero
    have hnorm := norms_of_product P I hP.ne_zero hI hn
    letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨i,hi⟩ := classify P hnorm.1
    have hpclass : ClassGroup.mk0 ⟨P,hPnz⟩∈S := by
      subst P
      exact hS i
    change ClassGroup.mk0 (⟨P,hPnz⟩*⟨I,hInz⟩)∈S
    rw [map_mul]
    exact S.mul_mem hpclass (ih hInz hnorm.2)
/-- All classes of the full native integer ring, not just analytic labels. -/
lemma every_class_mem (S:Subgroup (ClassGroup O))
    (hS:∀i:Fin 4,primeClass i∈S) (C:ClassGroup O) : C∈S := by
  obtain ⟨I,hC,hn⟩ :=
    PELOriginalCM210BoundedClassRepresentatives318.bounded_representative C
  rw [←hC]
  exact bounded_class_mem S hS I I.property hn
lemma closure_eq_top :
    Subgroup.closure (Set.range primeClass)=⊤ := by
  apply top_unique
  intro C _
  apply every_class_mem
  intro i
  exact Subgroup.subset_closure ⟨i,rfl⟩
end PELOriginalCM210NativeClassGeneration318
