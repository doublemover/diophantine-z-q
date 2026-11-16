module
public import ActualTwoDescentCoordinateSymbols318
public section
noncomputable section
namespace ActualTwoDescentLocalClassification318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentTorsionComparison318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Necessary support-prime torsion comparisons and the actual residue
condition at3 for positive-second-coordinate representatives. This is NOT
a definition of the elliptic Selmer group or its full local image. -/
def Admissible (p : Option U → ℕ) (δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  (∀ i, ∃ a b : ZMod 2, localCode p δ u v i=a • torsionOne p i+b • torsionTwo p i) ∧
  jacobiSym (monomial p v : ℤ) 3=1

/-- The actual torsion and residue comparisons produce all three finite
equations consumed by the already constructed arithmetic package. -/
theorem actual_comparisons_to_equations (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (δ : ZMod 2) (u v : Option U → ZMod 2) (H : Admissible p δ u v) :
    laplacian p *ᵥ u+Matrix.diagonal (lambda p) *ᵥ v=δ • lambda p ∧
    (laplacian p+Matrix.diagonal (parity p)) *ᵥ v=0 ∧
    dotProduct (lambda p+parity p) v=0 := by
  refine ⟨?_,?_,(actual_three_condition p hp2 hp3 v).mp H.2⟩
  · funext i
    have hi := ((actual_torsion_comparison_iff p δ u v i).mp (H.1 i)).1
    simpa only [Pi.add_apply,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] using hi
  · funext i
    have hi := ((actual_torsion_comparison_iff p δ u v i).mp (H.1 i)).2
    simpa only [Matrix.add_mulVec,Pi.add_apply,Matrix.mulVec_diagonal,Pi.zero_apply] using hi

/-- Exact classification of the positive-second-coordinate comparison
space. No conclusion about its representation by rational points is made. -/
theorem actual_local_classification (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (δ : ZMod 2) (u v : Option U → ZMod 2) :
    Admissible p δ u v ↔ δ=0 ∧ v=0 ∧
      ∃ c e : ZMod 2, u=c • ones (Option U)+e • beta := by
  constructor
  · intro H
    obtain ⟨h1,h2,h3⟩ := actual_comparisons_to_equations p hp2 hp3 δ u v H
    exact C.local_coefficients u v δ h1 h2 h3
  · rintro ⟨rfl,rfl,c,e,rfl⟩
    have hK : laplacian p *ᵥ (c • ones (Option U)+e • beta)=0 := by
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,
        actual_laplacian_ones,C.beta_kernel,smul_zero,smul_zero,add_zero]
    constructor
    · intro i
      apply (actual_torsion_comparison_iff p 0 _ 0 i).mpr
      simp only [hK,Pi.zero_apply,Matrix.mulVec_zero,mul_zero,zero_mul,add_zero,and_self]
    · simp [monomial]

/-- Uniqueness of the two surviving coefficients follows from actual
beta=0 at q0 and beta=1 at an original beta prime. -/
theorem actual_class_coefficients_unique (beta : Option U → ZMod 2)
    (h0 : beta none=0) (b : U) (hb : beta (some b)=1)
    (c e c' e' : ZMod 2)
    (h : c • ones (Option U)+e • beta=c' • ones (Option U)+e' • beta) :
    c=c' ∧ e=e' := by
  have hq := congrFun h none
  have hB := congrFun h (some b)
  have hc : c=c' := by simpa [ones,h0,smul_eq_mul] using hq
  refine ⟨hc,?_⟩
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ones,hb,mul_one] at hB
  rw [hc] at hB
  exact add_left_cancel hB

end ActualTwoDescentLocalClassification318
