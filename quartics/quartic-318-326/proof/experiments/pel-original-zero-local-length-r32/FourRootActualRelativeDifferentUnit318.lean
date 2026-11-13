module
public import FourRootActualDifferentTower318
public import FourRootActualKaehlerNeighborhoods318
public section
noncomputable section
namespace FourRootActualRelativeDifferentUnit318
open scoped TensorProduct
open Polynomial FourRootActualFiniteBranchChart318 FourRootActualFractionField318
open FourRootActualResidueInertia318 FourRootNormalizedPointCharts318
open FourRootActualDifferentTower318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (i:Fin 4)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance branchDedekind:IsDedekindDomain (BranchBase b i):=ActualLinearRootDifferent318.dedekind (b i)
local instance branchAlgebra:Algebra (BranchBase b i) (A b):=(branchMap b i).toAlgebra
local instance relativeFinite:Module.Finite (BranchBase b i) (A b):=(relative_finite_free b i).1
local instance relativeFree:Module.Free (BranchBase b i) (A b):=(relative_finite_free b i).2
local instance openSourceAlgebra:Algebra (A b) (OpenOrder b i):=
  (FourRootActualBranchLocalization318.sourceMap b i).toAlgebra
local instance openSourceLocalization:IsLocalization.Away (denominator b i) (OpenOrder b i):=
  FourRootActualBranchLocalization318.source_localization b i
local instance openSourceTower:IsScalarTower (BranchBase b i) (A b) (OpenOrder b i):=by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap (BranchBase b i) (OpenOrder b i) x=
    FourRootActualBranchLocalization318.sourceMap b i (branchMap b i x)
  simp only [FourRootActualBranchLocalization318.sourceMap,branchMap,RingHom.comp_apply,
    AlgEquiv.apply_symm_apply,FourRootActualBranchLocalization318.regroupedToOpen]
  rw [RingHom.comp_apply,AlgHom.commutes,IsScalarTower.algebraMap_apply
    (BranchBase b i) (OpenBase b i) (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),
    AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i) (OpenOrder b i) x

/-- The actual full order is unramified OVER ITS SIGNED ROOT COORDINATE
at every actual point of the constructed principal branch chart. The
upstairs prime is produced by the genuine localized evaluation map. -/
theorem relative_unramified (p:FinitePoints b)
    (hp:denominator b i∉finitePrime b p):
    Algebra.IsUnramifiedAt (BranchBase b i) (finitePrime b p):=by
  let e:OpenOrder b i→+*ℂ:=IsLocalization.Away.lift (denominator b i)
    (IsUnit.mk0 (finiteEvaluation b p (denominator b i)) hp)
  let q:Ideal (OpenOrder b i):=RingHom.ker e
  letI:q.IsPrime:=RingHom.ker_isPrime e
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  have he:∀x:A b,e (algebraMap (A b) (OpenOrder b i) x)=finiteEvaluation b p x:=
    fun x=>IsLocalization.Away.lift_eq _ _ x
  letI:q.LiesOver (finitePrime b p):=⟨by
    ext x
    change e (algebraMap (A b) (OpenOrder b i) x)=0↔finiteEvaluation b p x=0
    rw [he]⟩
  have hd:denominator b i≠0:=by
    intro hz
    apply hp
    rw [hz]
    exact Ideal.zero_mem _
  letI:IsDomain (OpenOrder b i):=IsLocalization.Away.isDomain _ hd
  letI:Algebra.Etale (OpenBase b i) (OpenOrder b i):=(finite_free_etale b i).2.2
  letI:Algebra.FormallyUnramified (BranchBase b i) (OpenBase b i):=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (branchDenominator b i))
  letI:Algebra.FormallyUnramified (BranchBase b i) (OpenOrder b i):=
    Algebra.FormallyUnramified.comp (BranchBase b i) (OpenBase b i) (OpenOrder b i)
  letI:Algebra.FinitePresentation (BranchBase b i) (OpenBase b i):=
    IsLocalization.Away.finitePresentation (branchDenominator b i)
  letI:Algebra.EssFiniteType (BranchBase b i) (OpenOrder b i):=
    Algebra.EssFiniteType.comp (BranchBase b i) (OpenBase b i) (OpenOrder b i)
  letI:Algebra.IsUnramifiedAt (BranchBase b i) q:=inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (BranchBase b i) (finitePrime b p) q

/-- Thus the actual relative TRACE different has no factor at this
original prime. This is a proved local unit statement, not a global claim
that the eightfold relative order is everywhere étale. -/
theorem relative_trace_unit (p:FinitePoints b)
    (hp:denominator b i∉finitePrime b p):
    ¬finitePrime b p∣differentIdeal (BranchBase b i) (A b):=by
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  exact not_dvd_differentIdeal_iff.mpr (relative_unramified b hb i p hp)

theorem at_actual_branch (p:FinitePoints b) (hp:p.val.1=b i):
    ¬finitePrime b p∣differentIdeal (BranchBase b i) (A b):=
  relative_trace_unit b hb i p
    (FourRootActualKaehlerNeighborhoods318.finite_branch_neighborhood b hb p i hp)
end FourRootActualRelativeDifferentUnit318
