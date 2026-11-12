module
public import ActualTwoDescentProjectionKernel318
public section
noncomputable section
namespace ActualTwoDescentSupportConditions318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentProjectionKernel318
open ActualTwoDescentCore318 ActualTwoDescentDiagonalExtension318
open scoped Matrix BigOperators
set_option maxHeartbeats 16000000

@[expose] def supportVector {ι : Type*} (v : ι → ZMod 2) : Option ι → ZMod 2
  | none => 0
  | some i => v i

/-- The selector has ones at one beta-support member and at q0,
exactly as in the retained descent construction. -/
def selector {ι : Type*} (b : ι) : (Option ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := x (some b)+x none
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul]; ring

@[expose] def Conditions {ι : Type*} [Fintype ι]
    (A : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) (b : ι) : Prop :=
  (∀ x, projectedAction (completion A) (selector b) (supportVector v) x=0 ↔
    ∃ c d : ZMod 2, x=c • ones (Option ι)+d • supportVector v) ∧
  (∀ x, projectedAction (completion A) (selector b) (supportVector v) x ≠
    completion A *ᵥ supportVector v) ∧
  (∀ c d : ZMod 2, c • ones (Option ι)+d • supportVector v=0 → c=0 ∧ d=0)

/-- Actual nonsingular core plus actual marked beta member produces
both required kernel/image conditions, and proves the two kernel generators
independent. No Selmer-space/rank theorem is folded into this statement. -/
theorem actual_support_conditions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hA : IsUnit A) (v : ι → ZMod 2) (b : ι)
    (hvb : v b=1) : Conditions A v b := by
  have ha1 : selector b (ones (Option ι))=0 := by norm_num [selector,ones]
  have hav : selector b (supportVector v)=1 := by simp [selector,supportVector,hvb]
  have hker : ∀ x, completion A *ᵥ x=0 → ∃ c : ZMod 2, x=c • ones (Option ι) :=
    fun x hx => ⟨x none,actual_completion_kernel A hA x hx⟩
  refine ⟨actual_projected_kernel _ _ _ ha1 hav (actual_completion_ones A) hker,
    actual_lambda_not_image _ _ _ ha1 hav hker,?_⟩
  intro c d hcd
  have hc : c=0 := by
    simpa [ones,supportVector] using congrFun hcd none
  have hd : d=0 := by
    simpa [ones,supportVector,hvb,hc] using congrFun hcd (some b)
  exact ⟨hc,hd⟩

/-- Literal beta-support indicator in the original deleted core: one on
ALL original beta primes, zero on all d auxiliary I slots. -/
@[expose] def coreBeta (d : ℕ) : Option (Fin d) ⊕ Fin d → ZMod 2 :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- All newly adjoined theta primes have beta-indicator0. -/
@[expose] def extendVector {ι : Type*} (v : ι → ZMod 2) : (n : ℕ) → Index ι n → ZMod 2
  | 0 => v
  | n+1 => Sum.elim (extendVector v n) (fun _ => 0)

lemma actual_extend_base {ι : Type*} (v : ι → ZMod 2) (n : ℕ) (i : ι) :
    extendVector v n (baseEmbed ι n i)=v i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- One diagonal choice retains the first support's exact core and
produces the kernel/image conditions on BOTH support sizes. The free
second-support template off-diagonals are all preserved. This is the
actual simultaneous finite-linear-algebra producer, not a two-point theorem. -/
theorem actual_simultaneous_support_conditions (d : ℕ)
    (D : Matrix (Option (Fin d)) (Option (Fin d)) (ZMod 2))
    (hD : (∑ i, ∑ j, D i j)=1) (n : ℕ)
    (M : Matrix (Index (Option (Fin d) ⊕ Fin d) n)
      (Index (Option (Fin d) ⊕ Fin d) n) (ZMod 2))
    (hbase : M.submatrix (baseEmbed _ n) (baseEmbed _ n)=core d D) :
    Conditions (core d D) (coreBeta d) (Sum.inl none) ∧
      ∃ M', IsUnit M' ∧ (∀ i j, i ≠ j → M' i j=M i j) ∧
        M'.submatrix (baseEmbed _ n) (baseEmbed _ n)=core d D ∧
        Conditions M' (extendVector (coreBeta d) n) (baseEmbed _ n (Sum.inl none)) := by
  have hcore := actual_core_unit d D hD
  refine ⟨actual_support_conditions _ hcore _ _ rfl,?_⟩
  have hM : IsUnit (M.submatrix (baseEmbed _ n) (baseEmbed _ n)) := by rw [hbase]; exact hcore
  obtain ⟨M',hM',hoff,hkeep⟩ := actual_diagonal_extension n M hM
  refine ⟨M',hM',hoff,?_,actual_support_conditions M' hM' _ _ ?_⟩
  · ext i j
    exact (hkeep i j).trans (congrFun (congrFun hbase i) j)
  · rw [actual_extend_base]
    rfl

end ActualTwoDescentSupportConditions318
