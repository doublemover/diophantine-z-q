module
public import ActualTwoDescentSupportParity318
public section
noncomputable section
namespace ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentSymbolTable318 ActualTwoDescentSignReciprocity318
open ActualTwoDescentSupportParity318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Numerator is the COLUMN prime, denominator the ROW prime, exactly
as in the original descent equations. The diagonal is excluded. -/
def edges (p : ι → ℕ) : Matrix ι ι (ZMod 2) :=
  fun i j => if i=j then 0 else symbolBit (p j) (p i)
def parity (p : ι → ℕ) : ι → ZMod 2 := fun i => ((p i/2 : ℕ) : ZMod 2)
def laplacian (p : ι → ℕ) : Matrix ι ι (ZMod 2) :=
  edges p + Matrix.diagonal (fun i => ∑ j, edges p i j)
def outer (v w : ι → ZMod 2) : Matrix ι ι (ZMod 2) := fun i j => v i*w j

lemma outer_mulVec (v w x : ι → ZMod 2) :
    outer v w *ᵥ x=fun i => v i*dotProduct w x := by
  funext i
  simp only [Matrix.mulVec,dotProduct,outer,Finset.mul_sum,mul_assoc]

lemma actual_laplacian_ones (p : ι → ℕ) : laplacian p *ᵥ ones ι=0 := by
  funext i
  simpa [laplacian,Matrix.mulVec,dotProduct,ones,Finset.sum_add_distrib] using
    (actual_two_add (∑ j, edges p i j))

/-- Full matrix reciprocity, including its diagonal correction, proved
from the actual prime symbols rather than assumed for an abstract matrix. -/
theorem actual_laplacian_reciprocity (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) :
    laplacian p+(laplacian p).transpose=
      outer (parity p) (parity p)+Matrix.diagonal (parity p) := by
  ext i j
  by_cases he : i=j
  · subst j
    have hleft := actual_two_add (laplacian p i i)
    have hright : parity p i*parity p i+parity p i=0 := by
      generalize parity p i=s
      fin_cases s <;> norm_num
    simpa only [Matrix.add_apply,Matrix.transpose_apply,outer,Matrix.diagonal_apply_eq] using
      hleft.trans hright.symm
  · have hsym := actual_symbol_reciprocity (p j) (p i) (hp2 j) (hp2 i)
      (fun h => he (hd h).symm)
    simpa [laplacian,edges,outer,parity,he,Ne.symm he,mul_comm] using hsym

/-- The actual product11mod12 forces zero COLUMN sums as well as the
row sums built into K. This is the normalization used in the descent step. -/
theorem actual_laplacian_transpose_ones (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) :
    (laplacian p).transpose *ᵥ ones ι=0 := by
  have hs : (∑ i, parity p i)=1 := actual_total_parity p hp2 hn
  have he := congrArg (fun M : Matrix ι ι (ZMod 2) => M *ᵥ ones ι)
    (actual_laplacian_reciprocity p hd hp2)
  rw [Matrix.add_mulVec,actual_laplacian_ones,zero_add,Matrix.add_mulVec,outer_mulVec] at he
  funext i
  have hi := congrFun he i
  have hdiag : (Matrix.diagonal (parity p) *ᵥ ones ι) i=parity p i := by
    simp [Matrix.mulVec,dotProduct,ones]
  have hi' : ((laplacian p).transpose *ᵥ ones ι) i=parity p i+parity p i := by
    simpa only [Pi.add_apply,dotProduct,ones,mul_one,hs,hdiag] using hi
  exact hi'.trans (actual_two_add (parity p i))

end ActualTwoDescentPrimeLaplacian318
