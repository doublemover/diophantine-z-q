module
public import PELOriginalLevelThetaFourier318
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public section
noncomputable section
namespace PELOriginalLevelThetaIndependence318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaRealTorus318
open PELOriginalLevelTheta318 PELOriginalLevelThetaFourier318
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ) [NeZero N]
@[expose] def representative (r:Label N):Index:=((r.1.val:ℤ),(r.2.val:ℤ))
lemma residue_representative (r:Label N):residue N (representative N r)=r:=by
  apply Prod.ext <;> simp [residue,representative]
@[expose] def leading (r:Label N):ℂ:=
  PELOriginalScaledThetaConvergence318.term τ (1/(N:ℝ)) (representative N r) 0
lemma leading_nonzero (r:Label N):leading τ N r≠0:=Complex.exp_ne_zero _
lemma coefficient_representative (r s:Label N):
    PELOriginalLevelThetaFourier318.coefficient τ N s (representative N r)=
      if r=s then leading τ N r else 0:=by
  simp only [PELOriginalLevelThetaFourier318.coefficient,levelTerm,
    PELOriginalScaledThetaHolomorphy318.selectedTerm,accepts,residue_representative,leading]

/-- The actual N² continuous real-torus theta functions are independent:
one genuine Fourier coefficient isolates each characteristic, with its
explicit nonzero exponential coefficient. No dimension theorem assumed. -/
theorem torus_independent:
    LinearIndependent ℂ (PELOriginalLevelThetaFourier318.torusTheta τ N):=by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc r
  have h:=congrArg (fourierCoefficient (representative N r)) hc
  simp only [map_sum,map_smul,map_zero,fourier_exact τ hτ N,coefficient_representative] at h
  have he:c r*leading τ N r=0:=by simpa [smul_eq_mul] using h
  exact (mul_eq_zero.mp he).resolve_right (leading_nonzero τ N r)

/-- Formal linear independence of the actual entire functions on C²,
transferred through the proved full real-representative identity. -/
theorem entire_independent:LinearIndependent ℂ (levelTheta τ N):=by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply (Fintype.linearIndependent_iff.mp (torus_independent τ hτ N)) c
  ext q
  obtain ⟨x,rfl⟩:=torusPoint_surjective q
  have h:=congrFun hc (realPoint x)
  simpa [PELOriginalLevelThetaFourier318.real_evaluation τ hτ N] using h
end PELOriginalLevelThetaIndependence318
