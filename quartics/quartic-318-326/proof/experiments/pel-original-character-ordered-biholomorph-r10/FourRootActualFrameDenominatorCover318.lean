module
public import FourRootActualKaehlerNeighborhoods318
public import FourRootAffineSmooth318
public section
noncomputable section
namespace FourRootActualFrameDenominatorCover318
open Polynomial FourRootActualFiniteBranchChart318 FourRootAffineCoordinateRing318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (Ring b):=(Polynomial.aeval (coordinate b none)).toAlgebra
lemma denominator_roots(i:Fin 4):denominator b i=
    ∏j:Fin 3,(coordinate b (some (FourRootPivot318.indices i j.succ)))^2:=by
  rw [denominator,denominatorPolynomial,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change Polynomial.aeval (coordinate b none)
    (X-C (b (FourRootPivot318.indices i j.succ)))=_
  rw [map_sub,Polynomial.aeval_X,Polynomial.aeval_C,relation]
lemma denominator_not_mem(p:PrimeSpectrum (Ring b))(i:Fin 4)
    (h:∀j,j≠i→coordinate b (some j)∉p.asIdeal):denominator b i∉p.asIdeal:=by
  rw [denominator_roots]
  have hn:∀j:Fin 3,(coordinate b (some (FourRootPivot318.indices i j.succ)))^2∉p.asIdeal:=by
    intro j
    have hj:FourRootPivot318.indices i j.succ≠i:=by
      intro he
      exact other_distinct b i hb j (congrArg b he.symm)
    simpa only [sq,p.isPrime.mul_mem_iff_mem_or_mem,or_self] using h _ hj
  have aux:∀s:Finset (Fin 3),∏j∈s,(coordinate b (some (FourRootPivot318.indices i j.succ)))^2∉p.asIdeal:=by
    intro s
    induction s using Finset.induction_on with
    | empty=>simp [p.isPrime.ne_top]
    | @insert j s hjs ih=>
      rw [Finset.prod_insert hjs,p.isPrime.mul_mem_iff_mem_or_mem,not_or]
      exact ⟨hn j,ih⟩
  exact aux _
/-- The four intrinsic finite frame domains cover EVERY affine scheme
prime, not only its known complex-valued points. -/
theorem finite_cover(p:PrimeSpectrum (Ring b)):∃i,denominator b i∉p.asIdeal:=by
  by_cases h:∃i,coordinate b (some i)∈p.asIdeal
  · obtain ⟨i,hi⟩:=h
    exact ⟨i,denominator_not_mem b hb p i (fun j hji=>
      FourRootAffineSmooth318.distinct_roots_not_both b hb p hji.symm hi)⟩
  · push_neg at h
    exact ⟨0,denominator_not_mem b hb p 0 (fun j _=>h j)⟩

/-- On the whole normalized infinity affine scheme, either u is
invertible (hence the original finite chart applies), or the genuine
infinity intrinsic frame denominator is excluded from the prime. -/
theorem infinity_cover(p:PrimeSpectrum (FourRootInfinityCoordinateRing318.Ring b)):
    FourRootInfinityCoordinateRing318.coordinate b none∉p.asIdeal ∨
      FourRootActualInfinityKaehler318.denominator b hb∉p.asIdeal:=by
  by_cases hu:FourRootInfinityCoordinateRing318.coordinate b none∈p.asIdeal
  · right
    let c:=FourRootReciprocalBranchData318.branches b
    let e:=FourRootInfinityAffineComparison318.equivalence b hb
    let q:PrimeSpectrum (Ring c):=PrimeSpectrum.comap e.symm.toRingHom p
    have hzero:coordinate c (some 0)∈q.asIdeal:=by
      change e.symm (coordinate c (some 0))∈p.asIdeal
      have he:e (FourRootInfinityCoordinateRing318.coordinate b none)=coordinate c (some 0):=rfl
      rw [←he,AlgEquiv.symm_apply_apply]
      exact hu
    have hn:=denominator_not_mem c (FourRootReciprocalBranchData318.branches_injective b hb) q 0
      (fun j hj=>FourRootAffineSmooth318.distinct_roots_not_both c
        (FourRootReciprocalBranchData318.branches_injective b hb) q hj.symm hzero)
    exact hn
  · exact Or.inl hu
end FourRootActualFrameDenominatorCover318
