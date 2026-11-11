module
public import FiniteLaurentVectorFiltration318
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public section
noncomputable section
namespace FiniteLaurentWindowPresentation318
open FiniteLaurentVectorFiltration318 LaurentPolynomial
open scoped BigOperators
set_option maxHeartbeats 750000
universe u
variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- Independence of the ACTUAL finitely many Laurent coefficient vectors
over any commutative ring, not a field-only dimension argument. -/
lemma independent (S : Set ℤ) [Fintype S] :
    LinearIndependent R (fun p : ι × S => monomial (k := R) p.1 p.2.val) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg p
  have h := congrArg (fun v : V R ι => (v p.1).coeff p.2.val) hg
  simpa [monomial,Pi.single_apply,LaurentPolynomial.T_apply,Finset.sum_product] using h

/-- A finite Laurent coefficient window has an actual finite-free
presentation, even over a nonreduced/non-Noetherian coefficient ring. -/
lemma finitePresentation (S : Set ℤ) (hS : S.Finite) :
    Module.FinitePresentation R (supported (k := R) (ι := ι) S) := by
  letI : Fintype S := hS.fintype
  have he : supported (k := R) (ι := ι) S =
      Submodule.span R (Set.range (fun p : ι × S => monomial (k := R) p.1 p.2.val)) := by
    congr 1
    ext v
    constructor
    · rintro ⟨i,a,ha,rfl⟩
      exact ⟨(i,⟨a,ha⟩),rfl⟩
    · rintro ⟨⟨i,a⟩,rfl⟩
      exact ⟨i,a.val,a.property,rfl⟩
  rw [he]
  exact Module.FinitePresentation.of_equiv (independent R ι S).linearCombinationEquiv
end FiniteLaurentWindowPresentation318
