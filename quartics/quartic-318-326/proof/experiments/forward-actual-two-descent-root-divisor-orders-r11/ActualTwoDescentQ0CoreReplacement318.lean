module
public import ActualTwoDescentThetaDiagonal318
public section
noncomputable section
namespace ActualTwoDescentQ0CoreReplacement318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentMatrixCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma actual_fixed_core_edges (p p' : Option U → ℕ)
    (hfix : ∀ i, p' (some i)=p (some i)) (i j : U) :
    edges p' (some i) (some j)=edges p (some i) (some j) := by
  simp only [edges,hfix]

/-- The only deleted-core effect of replacing q0 is the explicitly
prescribed new q0-column bit in each row, hence a diagonal toggle. -/
theorem actual_laplacian_core_replacement (p p' : Option U → ℕ)
    (hfix : ∀ i, p' (some i)=p (some i)) (t : U → ZMod 2)
    (hbits : ∀ i, edges p' (some i) none=edges p (some i) none+t i) :
    (fun i j => laplacian p' (some i) (some j) : Matrix U U (ZMod 2))=
      (fun i j => laplacian p (some i) (some j))+Matrix.diagonal t := by
  have hrow (i : U) : (∑ k, edges p' (some i) k)=(∑ k, edges p (some i) k)+t i := by
    rw [Fintype.sum_option,Fintype.sum_option,hbits]
    simp_rw [actual_fixed_core_edges p p' hfix]
    ring
  ext i j
  simp only [laplacian,Matrix.add_apply,Matrix.diagonal_apply,Option.some.injEq,
    actual_fixed_core_edges p p' hfix]
  by_cases he : i=j
  · subst j
    simp only [if_true,hrow]
    ring
  · simp only [he,if_false,add_zero]

/-- K-sharp has the same exact diagonal change: lambda at every retained
row and the selector are unchanged when only the actual q0 prime changes. -/
theorem actual_sharp_core_replacement (p p' : Option U → ℕ)
    (hfix : ∀ i, p' (some i)=p (some i)) (a : Option U → ZMod 2) (t : U → ZMod 2)
    (hbits : ∀ i, edges p' (some i) none=edges p (some i) none+t i) :
    (fun i j => sharp p' a (some i) (some j) : Matrix U U (ZMod 2))=
      (fun i j => sharp p a (some i) (some j))+Matrix.diagonal t := by
  have hK := actual_laplacian_core_replacement p p' hfix t hbits
  ext i j
  have hij := congrFun (congrFun hK i) j
  have hλ : lambda p' (some i)=lambda p (some i) := by simp only [lambda,hfix]
  simp only [sharp,Matrix.add_apply,outer,hλ]
  rw [hij]
  ring

end ActualTwoDescentQ0CoreReplacement318
