module
public import ActualTwoDescentSimultaneousCoreChoice318
public section
noncomputable section
namespace ActualTwoDescentQ0BetaPreservation318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentQ0CoreReplacement318
open ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma zero_q0_coordinate (M : Matrix (Option U) (Option U) (ZMod 2))
    (v : Option U → ZMod 2) (hv : v none=0) (i : U) :
    (M *ᵥ v) (some i)=
      ((fun i j => M (some i) (some j) : Matrix U U (ZMod 2)) *ᵥ (fun j => v (some j))) i := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,hv,mul_zero,zero_add]

/-- A diagonal change disjoint from the beta support preserves its actual
kernel equation. The q0 row follows from the proved COLUMN normalization,
so no unproved reverse-prime-symbol condition is silently added. -/
theorem actual_q0_beta_preserved (p p' : Option U → ℕ)
    (hfix : ∀ i, p' (some i)=p (some i)) (t : U → ZMod 2)
    (hbits : ∀ i, edges p' (some i) none=edges p (some i) none+t i)
    (v : Option U → ZMod 2) (hv0 : v none=0) (htv : ∀ i, t i*v (some i)=0)
    (hv : laplacian p *ᵥ v=0)
    (hcol : (laplacian p').transpose *ᵥ ones (Option U)=0) : laplacian p' *ᵥ v=0 := by
  have hK := actual_laplacian_core_replacement p p' hfix t hbits
  have hrows (i : U) : (laplacian p' *ᵥ v) (some i)=0 := by
    rw [zero_q0_coordinate _ v hv0 i,hK,Matrix.add_mulVec]
    have hold : ((fun i j => laplacian p (some i) (some j) : Matrix U U (ZMod 2)) *ᵥ
        (fun j => v (some j))) i=0 := by
      rw [←zero_q0_coordinate _ v hv0 i,hv]
      rfl
    change ((fun i j => laplacian p (some i) (some j) : Matrix U U (ZMod 2)) *ᵥ
      (fun j => v (some j))) i+(Matrix.diagonal t *ᵥ (fun j => v (some j))) i=0
    rw [hold,zero_add]
    simpa [Matrix.mulVec,dotProduct] using htv i
  have hsum : dotProduct (ones (Option U)) (laplacian p' *ᵥ v)=0 := by
    rw [←Matrix.dotProduct_transpose_mulVec,hcol,dotProduct_zero]
  have hnone : (laplacian p' *ᵥ v) none=0 := by
    simpa only [dotProduct,ones,one_mul,Fintype.sum_option,hrows,Finset.sum_const_zero,add_zero] using hsum
  funext i
  cases i with
  | none => exact hnone
  | some i => exact hrows i

/-- In the old/theta partition, retaining all old q0 bits is enough;
the beta indicator is identically zero on the freely toggled theta slots. -/
theorem actual_theta_beta_preserved {J : Type*} [Fintype J] [DecidableEq J]
    (p p' : Option (U ⊕ J) → ℕ) (hfix : ∀ i, p' (some i)=p (some i))
    (hold : ∀ i : U, edges p' (some (Sum.inl i)) none=edges p (some (Sum.inl i)) none)
    (v : Option (U ⊕ J) → ZMod 2) (hv0 : v none=0)
    (hvJ : ∀ j : J, v (some (Sum.inr j))=0) (hv : laplacian p *ᵥ v=0)
    (hcol : (laplacian p').transpose *ᵥ ones (Option (U ⊕ J))=0) :
    laplacian p' *ᵥ v=0 := by
  let t : U ⊕ J → ZMod 2 := fun i => edges p' (some i) none-edges p (some i) none
  apply actual_q0_beta_preserved p p' hfix t _ v hv0 _ hv hcol
  · intro i
    dsimp [t]
    ring
  · intro i
    cases i with
    | inl i => simp only [t,hold,sub_self,zero_mul]
    | inr j => simp only [hvJ,mul_zero]

end ActualTwoDescentQ0BetaPreservation318
