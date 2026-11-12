module
public import FourRootActualRelativeCotangent318
public import FourRootActualInfinityRamification318
public section
noncomputable section
namespace FourRootActualKaehlerNeighborhoods318
open Polynomial FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualFiniteBranchChart318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (FourRootAffineCoordinateRing318.Ring b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
lemma finite_eval_polynomial (p:FinitePoints b) (f:ℂ[X]):
    finiteEvaluation b p (algebraMap ℂ[X] (FourRootAffineCoordinateRing318.Ring b) f)=
      Polynomial.eval p.val.1 f:=by
  have h:(finiteEvaluation b p).comp
      (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none))=
      Polynomial.aeval p.val.1:=by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply,Polynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun h f
lemma finite_eval_denominator (p:FinitePoints b) (i:Fin 4):
    finiteEvaluation b p (denominator b i)=
      ∏j:Fin 3,(p.val.1-b (FourRootPivot318.indices i j.succ)):=by
  rw [denominator,finite_eval_polynomial]
  simp only [denominatorPolynomial,FourRootAffineTensorPresentation318.radicand,
    Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
/-- Every actual point above branch i lies in this SAME whole Kähler
principal chart, irrespective of the other three root signs. -/
theorem finite_branch_neighborhood (p:FinitePoints b) (i:Fin 4) (hp:p.val.1=b i):
    denominator b i∉finitePrime b p:=by
  change finiteEvaluation b p (denominator b i)≠0
  rw [finite_eval_denominator,hp]
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>sub_ne_zero.mpr (other_distinct b i hb j))
theorem all_finite_neighborhoods (p:FinitePoints b):∃i:Fin 4,denominator b i∉finitePrime b p:=by
  by_cases h:∃i:Fin 4,p.val.1=b i
  · obtain ⟨i,hi⟩:=h
    exact ⟨i,finite_branch_neighborhood b hb p i hi⟩
  · refine ⟨0,?_⟩
    change finiteEvaluation b p (denominator b 0)≠0
    rw [finite_eval_denominator]
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>sub_ne_zero.mpr (fun he=>h ⟨_,he⟩))
/-- All eight actual infinity centers lie in the same independently
constructed infinity Kähler neighborhood; no sign component is dropped. -/
theorem infinity_neighborhood (p:InfinityPoints b) (hp:p.val.1=0):
    FourRootActualInfinityKaehler318.denominator b hb∉infinityPrime b p:=by
  let q:=FourRootActualInfinityRamification318.finitePoint b hb p
  have hq:q.val.1=FourRootReciprocalBranchData318.branches b 0:=by
    rw [FourRootActualInfinityRamification318.finitePoint_base,hp,
      zero_pow (by decide:2≠0),FourRootReciprocalBranchData318.branches_zero]
  have hn:=finite_branch_neighborhood (FourRootReciprocalBranchData318.branches b)
    (FourRootReciprocalBranchData318.branches_injective b hb) q 0 hq
  have he:finiteEvaluation (FourRootReciprocalBranchData318.branches b) q=
      (infinityEvaluation b p).comp (FourRootInfinityAffineComparison318.fromAffine b hb):=
    (FourRootAffineCoordinateRing318.pointEquiv (FourRootReciprocalBranchData318.branches b)).symm_apply_apply _
  change infinityEvaluation b p (FourRootActualInfinityKaehler318.denominator b hb)≠0
  change finiteEvaluation (FourRootReciprocalBranchData318.branches b) q
    (denominator (FourRootReciprocalBranchData318.branches b) 0)≠0 at hn
  rw [he] at hn
  exact hn
end FourRootActualKaehlerNeighborhoods318
