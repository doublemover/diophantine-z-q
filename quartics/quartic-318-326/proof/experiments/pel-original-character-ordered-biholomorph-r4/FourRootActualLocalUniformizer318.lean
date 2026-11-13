module
public import ActualLinearRootPrime318
public import FourRootActualLocalTraceDifferent318
public import Mathlib.RingTheory.DedekindDomain.Dvr
public section
noncomputable section
namespace FourRootActualLocalUniformizer318
open FourRootActualFiniteBranchChart318 FourRootActualFractionField318
open FourRootActualResidueInertia318 FourRootNormalizedPointCharts318
open FourRootActualLocalTraceDifferent318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (i:Fin 4)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance branchDedekind:IsDedekindDomain (BranchBase b i):=ActualLinearRootDifferent318.dedekind (b i)
local instance branchAlgebra:Algebra (BranchBase b i) (A b):=(FourRootActualDifferentTower318.branchMap b i).toAlgebra
local instance relativeFinite:Module.Finite (BranchBase b i) (A b):=
  (FourRootActualDifferentTower318.relative_finite_free b i).1
local instance relativeFree:Module.Free (BranchBase b i) (A b):=
  (FourRootActualDifferentTower318.relative_finite_free b i).2
local instance pointPrime(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
local instance rootPrime:(ActualLinearRootPrime318.prime (b i)).IsPrime:=
  (ActualLinearRootPrime318.maximal (b i)).isPrime
lemma evaluation_root(p:FinitePoints b):
    finiteEvaluation b p (FourRootAffineCoordinateRing318.coordinate b (some i))=p.val.2 i:=by
  have h:=(FourRootAffineCoordinateRing318.pointEquiv b).apply_symm_apply p
  exact congrArg (fun q:FinitePoints b=>q.val.2 i) h
lemma original_root_zero(p:FinitePoints b)(hp:p.val.1=b i):p.val.2 i=0:=by
  have h:=p.property i
  rw [hp,sub_self] at h
  exact pow_eq_zero h
include hb in
lemma liesOver(p:FinitePoints b)(hp:p.val.1=b i):
    (finitePrime b p).LiesOver (ActualLinearRootPrime318.prime (b i)):=by
  constructor
  apply (ActualLinearRootPrime318.maximal (b i)).eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance:((finitePrime b p).under (BranchBase b i)).IsPrime))
  rw [ActualLinearRootPrime318.prime_eq]
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl:=Set.mem_singleton_iff.mp hx
  change finiteEvaluation b p
    (FourRootActualDifferentTower318.branchMap b i (ActualLinearRootDifferent318.root (b i)))=0
  rw [FourRootActualDifferentTower318.branchMap_root,evaluation_root,original_root_zero b i p hp]

/-- The original signed root generates the maximal ideal of the actual
source stalk. This follows from genuine unramifiedness over the root
base and its actual residue prime, not from the square equation alone. -/
theorem maximal_eq(p:FinitePoints b)(hp:p.val.1=b i):
    IsLocalRing.maximalIdeal (Stalk b p)=Ideal.span {rootAt b p i}:=by
  let q:=ActualLinearRootPrime318.prime (b i)
  letI:(finitePrime b p).LiesOver q:=liesOver b hb i p hp
  letI:Algebra (Localization.AtPrime q) (Stalk b p):=
    Localization.AtPrime.algebraOfLiesOver q (finitePrime b p)
  letI:Algebra.IsUnramifiedAt (BranchBase b i) (finitePrime b p):=
    FourRootActualRelativeDifferentUnit318.relative_unramified b hb i p
      (FourRootActualKaehlerNeighborhoods318.finite_branch_neighborhood b hb p i hp)
  have hm:=((Algebra.isUnramifiedAt_iff_map_eq (BranchBase b i) q (finitePrime b p)).mp inferInstance).2
  rw [←hm,ActualLinearRootPrime318.prime_eq,Ideal.map_span]
  simp only [Set.image_singleton]
  congr 1
  rw [IsScalarTower.algebraMap_apply (BranchBase b i) (A b) (Stalk b p)]
  change algebraMap (A b) (Stalk b p)
    (FourRootActualDifferentTower318.branchMap b i (ActualLinearRootDifferent318.root (b i)))=_
  rw [FourRootActualDifferentTower318.branchMap_root]
  rfl

/-- Thus the local trace different is exactly the maximal ideal, with
one simple branch factor rather than only the same support. -/
theorem trace_eq_maximal(p:FinitePoints b)(hp:p.val.1=b i):
    traceAt b hb p=IsLocalRing.maximalIdeal (Stalk b p):=by
  rw [FourRootActualLocalTraceDifferent318.at_actual_branch b hb p i hp,maximal_eq b hb i p hp]
lemma source_root_ne_zero:FourRootAffineCoordinateRing318.coordinate b (some i)≠0:=by
  have hr:=ActualLinearRootPrime318.root_ne_zero (b i)
  have hi:Function.Injective (algebraMap (BranchBase b i) (A b)):=
    FaithfulSMul.algebraMap_injective _ _
  rw [←FourRootActualDifferentTower318.branchMap_root b i]
  exact (map_ne_zero_iff _ hi).mpr hr
lemma point_ne_bot(p:FinitePoints b)(hp:p.val.1=b i):finitePrime b p≠⊥:=by
  intro h
  have hm:FourRootAffineCoordinateRing318.coordinate b (some i)∈finitePrime b p:=by
    change finiteEvaluation b p _=0
    rw [evaluation_root,original_root_zero b i p hp]
  rw [h,Ideal.mem_bot] at hm
  exact source_root_ne_zero b hb i hm
lemma local_dvr(p:FinitePoints b)(hp:p.val.1=b i):
    IsDiscreteValuationRing (Stalk b p):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A b) (point_ne_bot b hb i p hp) (Stalk b p)
/-- The trace-different generator is a TRUE uniformizer of the actual
original source stalk, hence its coefficient is exactly one. -/
theorem actual_uniformizer(p:FinitePoints b)(hp:p.val.1=b i):
    Irreducible (rootAt b p i):=by
  letI:IsDiscreteValuationRing (Stalk b p):=local_dvr b hb i p hp
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact (map_ne_zero_iff _ (IsLocalization.injective (Stalk b p)
      (finitePrime b p).primeCompl_le_nonZeroDivisors)).mpr (source_root_ne_zero b hb i)
  · exact maximal_eq b hb i p hp
end FourRootActualLocalUniformizer318
