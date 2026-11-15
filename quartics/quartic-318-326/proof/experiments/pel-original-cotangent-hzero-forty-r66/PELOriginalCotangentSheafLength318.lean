module
public import FourRootActualSheafLengths318
public import PELOriginalContactSchemePoints318
public import PELOriginalZeroQuotientLengths318
public section
noncomputable section
namespace PELOriginalCotangentSheafLength318
open scoped OnePoint BigOperators Classical
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open FourRootNormalizedPointCharts318 FourRootCompletedSchemePoints318
/-- Length of the ACTUAL original global relative cotangent sheaf stalk
at the point of the SAME original source's complex-valued Scheme map,
over the actual structure-sheaf local ring with its canonical action. -/
@[expose] def length (p : UnlevelledBase) : ℕ∞ :=
  FourRootCotangentStalkQuotient318.length branches
    ((PELOriginalContactSchemePoints318.comparison p).val default)
/-- Exact sheaf-stalk/local-quotient comparison proved before counting. -/
theorem length_equals_local (p : UnlevelledBase) :
    length p = PELOriginalZeroQuotientLengths318.localLength p := by
  unfold length PELOriginalZeroQuotientLengths318.localLength
  rw [PELOriginalContactSchemePoints318.comparison_value]
  cases h : completedMap p with
  | inl q => exact FourRootActualSheafLengths318.finite_length branches branches_injective q
  | inr s => exact FourRootActualSheafLengths318.infinity_length branches branches_injective
      (center branches s) rfl
/-- The numerical coefficients are consequences of actual sheaf-stalk
module isomorphisms and the previous exact original local quotient computation. -/
theorem length_equals_different (p : UnlevelledBase) :
    length p = (PELOriginalActualDifferentDivisor318.coefficient p : ℕ∞) :=
  (length_equals_local p).trans (PELOriginalZeroQuotientLengths318.length_equals_different p)
theorem branch_length (p : UnlevelledBase) (hp : p ∈ nontrivialStabilizerLocus) :
    length p = 1 :=
  (length_equals_local p).trans (PELOriginalZeroQuotientLengths318.branch_length p hp)
theorem regular_length (p : UnlevelledBase) (hp : p ∈ RegularSource) : length p = 0 :=
  (length_equals_local p).trans (PELOriginalZeroQuotientLengths318.regular_length p hp)
/-- Sum of the true original relative cotangent SHEAF stalk lengths at
all forty original ramification points. The indexing is the original
ramification carrier, each point occurring once, not a replacement divisor. -/
theorem total_sheaf_stalk_length_forty :
    (∑ p : PELOriginalFiniteRamification318.Ramification, length p.val) = 40 := by
  simp_rw [length_equals_local]
  exact PELOriginalZeroQuotientLengths318.total_length_forty
end PELOriginalCotangentSheafLength318
