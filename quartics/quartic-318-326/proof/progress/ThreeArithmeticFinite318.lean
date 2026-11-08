module
public import ActualJAllLevels318
public import ThreeArithmeticSurjective318
public section
noncomputable section
namespace ThreeArithmeticFinite318
open OpenJModel318 ThreeArithmeticQuotient318

/-- The actual analytic-to-arithmetic comparison is finite-to-one. This
uses the proved genuine j-compatibility and actual finite j-fibers, not an
assumed modular classification or injectivity premise. -/
theorem finite_fiber (N : ℕ) [NeZero N] (f : LiteralThreeXComparison318.Fixed N →+* ℂ) :
    ((complexPoint N) ⁻¹' {f}).Finite := by
  have hj := ActualJAllLevels318.finite_fiber 3
    (f (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N)))
  have hs : ((complexPoint N) ⁻¹' {f}) ⊆ Subtype.val ⁻¹'
      ((QuotientJ318.jMap 3) ⁻¹' {f (algebraMap (Base N)
        (LiteralThreeXComparison318.Fixed N) (jCoord N))}) := by
    intro q hq
    change complexPoint N q=f at hq
    change QuotientJ318.jMap 3 q.val=f _
    rw [←complexPoint_j N q,hq]
  exact (hj.preimage Subtype.val_injective.injOn).subset hs

/-- A global finite-to-one surjection from the actual admissible modular
quotient to complex points of the specified arithmetic fixed algebra. This
is still weaker than injectivity or an analytic/algebraic isomorphism. -/
theorem finite_surjection (N : ℕ) [NeZero N] :
    Function.Surjective (complexPoint N) ∧
      ∀f : LiteralThreeXComparison318.Fixed N →+* ℂ, ((complexPoint N) ⁻¹' {f}).Finite :=
  ⟨ThreeArithmeticSurjective318.complexPoint_surjective N,finite_fiber N⟩

end ThreeArithmeticFinite318
