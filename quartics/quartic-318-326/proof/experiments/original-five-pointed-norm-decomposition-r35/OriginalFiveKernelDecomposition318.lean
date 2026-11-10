module
public import OriginalFiveKernelCoordinates318
public section
noncomputable section
namespace OriginalFiveKernelDecomposition318
open ActualFiveHOneDecomposition318 ActualSourceHOnePullbacks318
open OriginalFiveKernelCoordinates318
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Tensor product of the FIVE OLD line-class pullbacks on the ORIGINAL
special-fiber kernels. This forward map is not defined by H1 conjugation. -/
@[expose] def product : ((i : Index) → TargetKernel i) →* SourceKernel where
  toFun x := ∏ i, OriginalFiveKernelCoordinates318.pullback i (x i)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply,map_mul,Finset.prod_mul_distrib]
lemma source_sum (q : (i : Index) → SourceHOne) :
    source (Multiplicative.ofAdd (∑ i,q i)) = ∏ i,source (Multiplicative.ofAdd (q i)) := by
  classical
  have hs (s : Finset Index) : source (Multiplicative.ofAdd (∑ i ∈ s,q i)) =
      ∏ i ∈ s,source (Multiplicative.ofAdd (q i)) := by
    induction s using Finset.induction_on with
    | empty => exact map_one source
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi]
      change source (Multiplicative.ofAdd (q i) * Multiplicative.ofAdd (∑ j ∈ s,q j)) = _
      rw [map_mul,ih]
  exact hs Finset.univ
lemma product_coordinates (q : (i : Index) → TargetHOne i) :
    product (fun i => target i (Multiplicative.ofAdd (q i))) =
      source (Multiplicative.ofAdd (OriginalFiveHOneTraceEquivalence318.equivalence q)) := by
  change (∏ i,OriginalFiveKernelCoordinates318.pullback i (target i (Multiplicative.ofAdd (q i)))) = _
  simp only [pullback_target,OriginalFiveHOneTraceEquivalence318.equivalence_apply,source_sum]
@[expose] def targetCoordinates (i : Index) : TargetKernel i ≃ TargetHOne i where
  toFun x := ((target i).symm x).toAdd
  invFun y := target i (Multiplicative.ofAdd y)
  left_inv x := (target i).apply_symm_apply x
  right_inv y := congrArg Multiplicative.toAdd ((target i).symm_apply_apply (Multiplicative.ofAdd y))
@[expose] def sourceCoordinates : SourceKernel ≃ SourceHOne where
  toFun x := (source.symm x).toAdd
  invFun y := source (Multiplicative.ofAdd y)
  left_inv x := source.apply_symm_apply x
  right_inv y := congrArg Multiplicative.toAdd (source.symm_apply_apply (Multiplicative.ofAdd y))
/-- The old H1 theorem and actual kernel classifications supply bijectivity;
the next theorem identifies the forward map with ORIGINAL tensor pullbacks. -/
@[expose] def coordinateEquivalence : ((i : Index) → TargetKernel i) ≃ SourceKernel :=
  (Equiv.piCongrRight targetCoordinates).trans
    (OriginalFiveHOneTraceEquivalence318.equivalence.toEquiv.trans sourceCoordinates.symm)
lemma coordinateEquivalence_apply (x : (i : Index) → TargetKernel i) :
    coordinateEquivalence x = product x := by
  have h := product_coordinates (fun i => targetCoordinates i (x i))
  have hx : (fun i => target i (Multiplicative.ofAdd (targetCoordinates i (x i)))) = x := by
    funext i
    exact (target i).apply_symm_apply (x i)
  rw [hx] at h
  exact h.symm
lemma product_bijective : Function.Bijective product := by
  have he : (product : _ → _) = coordinateEquivalence :=
    funext (fun x => (coordinateEquivalence_apply x).symm)
  rw [he]
  exact coordinateEquivalence.bijective
/-- Actual tensor-group decomposition of the WHOLE original first-order
Picard kernel by the SAME five original quotient pullbacks. -/
@[expose] def equivalence : ((i : Index) → TargetKernel i) ≃* SourceKernel :=
  MulEquiv.ofBijective product product_bijective
lemma equivalence_apply (x : (i : Index) → TargetKernel i) :
    equivalence x = ∏ i,OriginalFiveKernelCoordinates318.pullback i (x i) := rfl
/-- Inverse components are the ORIGINAL normalized trace/8 coordinates,
not unspecified complements of each individual split injection. -/
lemma inverse_component (L : SourceKernel) (i : Index) :
    equivalence.symm L i = target i (Multiplicative.ofAdd
      (ActualFiveHOneDecomposition318.transfer i (sourceCoordinates L))) := by
  have h := product_coordinates
    (fun j => ActualFiveHOneDecomposition318.transfer j (sourceCoordinates L))
  rw [← OriginalFiveHOneTraceEquivalence318.equivalence_symm,
    LinearEquiv.apply_symm_apply] at h
  have hall : equivalence.symm L = fun j => target j (Multiplicative.ofAdd
      (ActualFiveHOneDecomposition318.transfer j (sourceCoordinates L))) := by
    apply equivalence.injective
    rw [MulEquiv.apply_symm_apply]
    exact (h.trans (source.apply_symm_apply L)).symm
  exact congrArg (fun x => x i) hall
/-- The actual raw determinant norms compose with the five old pullbacks to
the EIGHTH tensor power on the original first-order kernel. -/
lemma product_norms (L : SourceKernel) :
    ∏ i,OriginalFiveKernelCoordinates318.pullback i (norm i L) = L ^ 8 := by
  obtain ⟨z,rfl⟩ := source.surjective L
  change (∏ i,OriginalFiveKernelCoordinates318.pullback i (norm i (source (Multiplicative.ofAdd z.toAdd)))) = _
  simp only [norm_source,pullback_target,← source_sum]
  rw [OriginalFiveHOneNormMatrices318.sum_pullback_traces]
  simpa only [Nat.cast_smul_eq_nsmul] using map_pow source (Multiplicative.ofAdd z.toAdd) 8
end OriginalFiveKernelDecomposition318
