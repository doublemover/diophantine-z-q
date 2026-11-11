module
public import FourRootActualDifferentTower318
public import FourRootActualKaehlerNeighborhoods318
public import Mathlib.RingTheory.Localization.Ideal
public section
noncomputable section
namespace FourRootAllPrimeRelativeDifferent318
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

/-- Relative unramifiedness on the actual root chart at EVERY prime,
not just the original complex evaluation kernels. The upstairs prime is
produced by true localization and carries its exact lies-over equality. -/
theorem relative_unramified (p:Ideal (A b)) [p.IsPrime]
    (hp:denominator b i∉p):Algebra.IsUnramifiedAt (BranchBase b i) p:=by
  have hM:Disjoint (Submonoid.powers (denominator b i):Set (A b)) (p:Set (A b)):=by
    apply Set.disjoint_left.mpr
    rintro x ⟨n,rfl⟩ hx
    exact (p.primeCompl.pow_mem hp n) hx
  let q:Ideal (OpenOrder b i):=p.map (algebraMap (A b) (OpenOrder b i))
  letI:q.IsPrime:=IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (denominator b i)) (OpenOrder b i) p inferInstance hM
  letI:q.LiesOver p:=IsLocalization.liesOver_map_of_isPrime_disjoint
    (Submonoid.powers (denominator b i)) (OpenOrder b i) hM
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
  exact Algebra.IsUnramifiedAt.of_liesOver (BranchBase b i) (p) q

/-- Exact trace-dual different unit criterion, still relative to the
original signed root and valid at all original affine primes. -/
theorem relative_trace_unit (p:Ideal (A b)) [p.IsPrime]
    (hp:denominator b i∉p):¬p∣differentIdeal (BranchBase b i) (A b):=by
  exact not_dvd_differentIdeal_iff.mpr (relative_unramified b hb i p hp)
end FourRootAllPrimeRelativeDifferent318
