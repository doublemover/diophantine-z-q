module
public import ActualTwoDescentMatrixCompletion318
public section
noncomputable section
namespace ActualTwoDescentArithmeticKernel318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentThreeSymbol318 ActualTwoDescentMatrixCompletion318
open ActualTwoDescentProjectionKernel318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

def dotLinear {ι : Type*} [Fintype ι] (a : ι → ZMod 2) :
    (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := dotProduct a
  map_add' := fun x y => dotProduct_add a x y
  map_smul' := fun r x => dotProduct_smul r a x

lemma actual_sharp_beta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (a v : ι → ZMod 2)
    (hv : laplacian p *ᵥ v=0) (hav : dotProduct a v=1) :
    sharp p a *ᵥ v=lambda p := by
  rw [sharp,Matrix.add_mulVec,hv,zero_add,outer_mulVec]
  funext i
  rw [hav,mul_one]

/-- The projection identity holds for the actual arithmetic matrix K,
with its literal beta vector and lambda, not just for a model operator. -/
lemma actual_arithmetic_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (a v : ι → ZMod 2)
    (hv : laplacian p *ᵥ v=0) (hav : dotProduct a v=1) (x : ι → ZMod 2) :
    projectedAction (sharp p a) (dotLinear a) v x=laplacian p *ᵥ x := by
  rw [projectedAction,Matrix.mulVec_sub,Matrix.mulVec_smul,actual_sharp_beta p a v hv hav]
  change (laplacian p+outer (lambda p) a) *ᵥ x-
    dotProduct a x • lambda p=laplacian p *ᵥ x
  rw [Matrix.add_mulVec,outer_mulVec]
  funext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Connect the actual arithmetic K-sharp deleted core to the precise
kernel and excluded-image conclusions used in two-descent. The remaining
core/unit and beta-row obligations are stated on this same arithmetic K. -/
theorem actual_arithmetic_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Option ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a v : Option ι → ZMod 2) (ha : ∑ i, a i=0)
    (hv : laplacian p *ᵥ v=0) (hav : dotProduct a v=1)
    (hcore : IsUnit (fun i j => sharp p a (some i) (some j) : Matrix ι ι (ZMod 2))) :
    (∀ x, laplacian p *ᵥ x=0 ↔
      ∃ c d : ZMod 2, x=c • ones (Option ι)+d • v) ∧
    (∀ x, laplacian p *ᵥ x ≠ lambda p) := by
  let M := sharp p a
  let A : Matrix ι ι (ZMod 2) := fun i j => M (some i) (some j)
  have he : M=completion A := actual_sharp_completion p hd hp2 hp3 hn a ha
  have hker : ∀ x, M *ᵥ x=0 → ∃ c : ZMod 2, x=c • ones (Option ι) := by
    intro x hx
    rw [he] at hx
    exact ⟨x none,actual_completion_kernel A hcore x hx⟩
  have hMone : M *ᵥ ones (Option ι)=0 :=
    (actual_sharp_normalization p hd hp2 hp3 hn a ha).1
  have haone : dotLinear a (ones (Option ι))=0 := by
    simpa only [dotLinear,dotProduct,ones,mul_one] using ha
  have hMv : M *ᵥ v=lambda p := actual_sharp_beta p a v hv hav
  constructor
  · intro x
    rw [←actual_arithmetic_projection p a v hv hav x]
    exact actual_projected_kernel M (dotLinear a) v haone hav hMone hker x
  · intro x hx
    apply actual_lambda_not_image M (dotLinear a) v haone hav hker x
    rw [actual_arithmetic_projection p a v hv hav x,hMv]
    exact hx

end ActualTwoDescentArithmeticKernel318
