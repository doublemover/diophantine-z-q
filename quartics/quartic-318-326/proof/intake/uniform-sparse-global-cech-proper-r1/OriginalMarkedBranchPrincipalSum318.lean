module
public import OriginalSparseActualBranch318
public import OriginalBranchCechOverlap318
public section
noncomputable section
namespace OriginalMarkedBranchPrincipalSum318
open Polynomial OriginalUniversalSparsePolynomial318 OriginalSparseActualBranch318
open OriginalBranchPlaneLocal318 OriginalBranchResidueLocal318 OriginalSexticJetMarked318
open OriginalSexticJetResidues318 OriginalUniformSparseSmoothChart318
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
omit [Algebra E L] in
theorem map_sextic (σ : E →+* L) (s t : E) : (sextic s t).map σ=sextic (σ s) (σ t) := by
  simp [sextic,cvec,pol,map_ofNat]
variable (J : Certificate E L) (s t : E) (hF : J.F=sextic s t)
include hF
theorem branch_point (p : Fin 6) :
    eqVal (algebraMap E L s) (algebraMap E L t) (J.labels p)=0 := by
  rw [← polynomial_eq,←map_sextic,←hF,J.factorization,split_eval]
theorem branch_partial (p : Fin 6) :
    derVal (algebraMap E L s) (algebraMap E L t) (J.labels p)=branchSlope J p := by
  rw [←derivative_eq,←map_sextic,←hF,J.factorization,branchSlope]
theorem partial_ne (p : Fin 6) :
    derVal (algebraMap E L s) (algebraMap E L t) (J.labels p)≠0 :=
  (branch_partial J s t hF p).symm ▸ branchSlope_ne J p

/-- One residue obtained by specializing the REGULAR logarithmic numerator in
the maximal local ring of the actual sparse affine curve at this named branch. -/
@[expose] def residue (i j : ℕ) (p : Fin 6) : L :=
  let a:=algebraMap E L s
  let b:=algebraMap E L t
  let h:=branch_point J s t hF p
  let h₁:=partial_ne J s t hF p
  let φ:=ev a b (J.labels p) h
  specialize φ (principalNumerator φ (OriginalUniformSparseAffineModel318.x a b)
    (sextic a b) (J.G.map (algebraMap E L)) i j (unit_jac a b (J.labels p) h h₁))
theorem on_branch (i j : ℕ) (p : Fin 6) :
    residue J s t hF i j p = -2*(J.labels p)^(i+j)*(J.G.map (algebraMap E L)).eval (J.labels p)/(branchSlope J p)^2 := by
  unfold residue
  rw [local_read _ _ _ _ (partial_ne J s t hF p),branch_partial J s t hF p]
theorem sum_is_trace (i j : ℕ) (k : Fin 3) (hk : i+j=(k:ℕ)) :
    ∑ p,residue J s t hF i j p=algebraMap E L (moment J k) := by
  rw [moment_eq_branch,branchMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [on_branch,hk]
  ring
@[expose] def determinant : L :=
  (∑ p,residue J s t hF 0 0 p)*(∑ p,residue J s t hF 1 1 p)-
    (∑ p,residue J s t hF 0 1 p)^2
theorem det_is_raw : determinant J s t hF=algebraMap E L (rawB J) := by
  simp only [determinant,sum_is_trace J s t hF 0 0 0 (by decide),
    sum_is_trace J s t hF 1 1 2 (by decide),sum_is_trace J s t hF 0 1 1 (by decide),rawB,map_sub,map_mul,map_pow]
end OriginalMarkedBranchPrincipalSum318
#print axioms OriginalMarkedBranchPrincipalSum318.det_is_raw
