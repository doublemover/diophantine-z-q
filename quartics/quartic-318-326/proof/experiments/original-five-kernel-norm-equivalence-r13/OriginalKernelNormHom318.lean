module
public import OriginalFiveKernelDecomposition318
public section
noncomputable section
namespace OriginalKernelNormHom318
open OriginalFiveKernelCoordinates318
open ActualFiveHOneDecomposition318 ActualSourceHOnePullbacks318
/-- The existing determinant norm preserves the existing tensor identity. -/
lemma norm_one (i : Index) : norm i 1 = 1 := by
  have h := norm_source i 0
  change norm i (source 1) = target i (Multiplicative.ofAdd
    (OriginalHOneTraceNormalization318.originalTrace i 0)) at h
  rw [map_one,map_zero] at h
  exact h.trans (map_one (target i))
/-- Tensor multiplicativity of the SAME genuine first-order determinant norm,
proved using the already identified original raw trace, not a replacement map. -/
lemma norm_mul (i : Index) (L M : SourceKernel) : norm i (L * M) = norm i L * norm i M := by
  obtain ⟨x,rfl⟩ := source.surjective L
  obtain ⟨y,rfl⟩ := source.surjective M
  rw [← map_mul]
  change norm i (source (Multiplicative.ofAdd (x.toAdd + y.toAdd))) =
    norm i (source (Multiplicative.ofAdd x.toAdd)) * norm i (source (Multiplicative.ofAdd y.toAdd))
  rw [norm_source,norm_source,norm_source,map_add]
  exact map_mul (target i) (Multiplicative.ofAdd _) (Multiplicative.ofAdd _)
@[expose] def hom (i : Index) : SourceKernel →* TargetKernel i where
  toFun := norm i
  map_one' := norm_one i
  map_mul' := norm_mul i
lemma hom_apply (i : Index) (L : SourceKernel) : hom i L = norm i L := rfl
/-- The raw norm matrix has degree EIGHT on its own original factor. -/
lemma diagonal (i : Index) (L : TargetKernel i) : hom i (OriginalFiveKernelCoordinates318.pullback i L) = L ^ 8 := by
  obtain ⟨x,rfl⟩ := (target i).surjective L
  change norm i (OriginalFiveKernelCoordinates318.pullback i (target i (Multiplicative.ofAdd x.toAdd))) = _
  rw [pullback_target,norm_source,OriginalFiveHOneNormMatrices318.trace_pullback_matrix,dif_pos rfl]
  simpa only [Nat.cast_smul_eq_nsmul] using map_pow (target i) (Multiplicative.ofAdd x.toAdd) 8
/-- Every wrong-character ORIGINAL norm-pullback is trivial, on whole kernels. -/
lemma off_diagonal (i j : Index) (hij : i ≠ j) (L : TargetKernel j) : hom i (OriginalFiveKernelCoordinates318.pullback j L) = 1 := by
  obtain ⟨x,rfl⟩ := (target j).surjective L
  change norm i (OriginalFiveKernelCoordinates318.pullback j (target j (Multiplicative.ofAdd x.toAdd))) = _
  rw [pullback_target,norm_source,OriginalFiveHOneNormMatrices318.trace_pullback_matrix,dif_neg hij]
  exact map_one (target i)
end OriginalKernelNormHom318
