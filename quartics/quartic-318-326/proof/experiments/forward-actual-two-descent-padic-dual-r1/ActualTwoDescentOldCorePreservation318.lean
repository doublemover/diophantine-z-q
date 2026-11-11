module
public import ActualTwoDescentQ0PrimeReplacement318
public section
noncomputable section
namespace ActualTwoDescentOldCorePreservation318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentMatrixCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

def oldEmbedding : Option U → Option (U ⊕ J)
  | none => none
  | some i => some (Sum.inl i)
def restricted (p : Option (U ⊕ J) → ℕ) : Option U → ℕ := p ∘ oldEmbedding
def restrictedSelector (a : Option (U ⊕ J) → ZMod 2) : Option U → ZMod 2 := a ∘ oldEmbedding

lemma actual_restricted_edges (p : Option (U ⊕ J) → ℕ) (i j : Option U) :
    edges (restricted p) i j=edges p (oldEmbedding i) (oldEmbedding j) := by
  cases i <;> cases j <;> simp [edges,restricted,oldEmbedding]

/-- The actual product on the enlarged support is the old twist times
the literal theta-prime product, with q0 included exactly once. -/
lemma actual_product_split (p : Option (U ⊕ J) → ℕ) :
    (∏ i, p i)=(∏ i, restricted p i)*(∏ j : J, p (some (Sum.inr j))) := by
  simp only [Fintype.prod_option,Fintype.prod_sum_type,restricted,Function.comp_apply,oldEmbedding]
  ring

/-- Mutual-square row sums and zero I/theta symbols retain EVERY entry
of the actual old K-sharp core when theta is adjoined. -/
theorem actual_old_core_preserved (p : Option (U ⊕ J) → ℕ)
    (a : Option (U ⊕ J) → ZMod 2)
    (hcross : ∀ i : U, (∑ j : J, edges p (some (Sum.inl i)) (some (Sum.inr j)))=0) :
    (fun i j => sharp p a (some (Sum.inl i)) (some (Sum.inl j)) : Matrix U U (ZMod 2))=
      (fun i j => sharp (restricted p) (restrictedSelector a) (some i) (some j)) := by
  have hrow (i : U) : (∑ k, edges p (some (Sum.inl i)) k)=
      ∑ k, edges (restricted p) (some i) k := by
    rw [Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_option,hcross,add_zero]
    simp_rw [actual_restricted_edges]
    rfl
  ext i j
  have he := actual_restricted_edges p (some i) (some j)
  simp only [oldEmbedding] at he
  simp only [sharp,Matrix.add_apply,outer,laplacian,Matrix.add_apply,Matrix.diagonal_apply,
    Option.some.injEq,Sum.inl.injEq,←he,hrow,lambda,restricted,restrictedSelector,
    Function.comp_apply,oldEmbedding]

end ActualTwoDescentOldCorePreservation318
