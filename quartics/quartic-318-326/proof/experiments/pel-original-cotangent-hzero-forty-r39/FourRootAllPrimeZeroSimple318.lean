module
public import FourRootAllPrimeFiniteDifferent318
public import ActualLinearRootPrime318
public section
noncomputable section
namespace FourRootAllPrimeZeroSimple318
open Polynomial FourRootActualFiniteBranchChart318 FourRootActualFractionField318
open FourRootActualDifferentTower318 FourRootDerivativeZeroIdeals318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
abbrev Stalk(p:Ideal (A b))[p.IsPrime]:=Localization.AtPrime p
variable (i:Fin 4)
local instance branchDedekind:IsDedekindDomain (BranchBase b i):=ActualLinearRootDifferent318.dedekind (b i)
local instance branchAlgebra:Algebra (BranchBase b i) (A b):=(branchMap b i).toAlgebra
local instance relativeFinite:Module.Finite (BranchBase b i) (A b):=(relative_finite_free b i).1
local instance relativeFree:Module.Free (BranchBase b i) (A b):=(relative_finite_free b i).2
local instance rootPrime:(ActualLinearRootPrime318.prime (b i)).IsPrime:=
  (ActualLinearRootPrime318.maximal (b i)).isPrime
/-- Any original scheme prime containing the signed root lies over the
actual root-zero prime. No realization as a complex point is assumed. -/
include hb in
lemma liesOver (p:Ideal (A b))[p.IsPrime]
    (hz:FourRootAffineCoordinateRing318.coordinate b (some i)∈p):
    p.LiesOver (ActualLinearRootPrime318.prime (b i)):=by
  constructor
  apply (ActualLinearRootPrime318.maximal (b i)).eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance:(p.under (BranchBase b i)).IsPrime))
  rw [ActualLinearRootPrime318.prime_eq]
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl:=Set.mem_singleton_iff.mp hx
  change branchMap b i (ActualLinearRootDifferent318.root (b i))∈p
  rw [branchMap_root]
  exact hz
/-- Exact maximal ideal of EVERY original prime-local ring above the
root-zero locus, from actual relative unramifiedness. -/
theorem maximal_eq (p:Ideal (A b))[p.IsPrime]
    (hz:FourRootAffineCoordinateRing318.coordinate b (some i)∈p)
    (hp:denominator b i∉p):
    IsLocalRing.maximalIdeal (Stalk b p)=
      Ideal.span {algebraMap (A b) (Stalk b p) (FourRootAffineCoordinateRing318.coordinate b (some i))}:=by
  let q:=ActualLinearRootPrime318.prime (b i)
  letI:p.LiesOver q:=liesOver b hb i p hz
  letI:Algebra (Localization.AtPrime q) (Stalk b p):=
    Localization.AtPrime.algebraOfLiesOver q p
  letI:Algebra.IsUnramifiedAt (BranchBase b i) p:=
    FourRootAllPrimeRelativeDifferent318.relative_unramified b hb i p hp
  have hm:=((Algebra.isUnramifiedAt_iff_map_eq (BranchBase b i) q p).mp inferInstance).2
  rw [←hm,ActualLinearRootPrime318.prime_eq,Ideal.map_span]
  simp only [Set.image_singleton]
  congr 1
  rw [IsScalarTower.algebraMap_apply (BranchBase b i) (A b) (Stalk b p)]
  change algebraMap (A b) (Stalk b p)
    (branchMap b i (ActualLinearRootDifferent318.root (b i)))=_
  rw [branchMap_root]
/-- The original whole zero ideal at EVERY prime is either the unit
ideal or the actual maximal ideal, with no radical replacement. -/
theorem local_dichotomy (p:Ideal (A b))[p.IsPrime]:
    (finiteIdeal b).map (algebraMap (A b) (Stalk b p))=⊤ ∨
    (finiteIdeal b).map (algebraMap (A b) (Stalk b p))=
      IsLocalRing.maximalIdeal (Stalk b p):=by
  classical
  obtain ⟨j,hj⟩:=FourRootActualFrameDenominatorCover318.finite_cover b hb ⟨p,inferInstance⟩
  have he:=FourRootAllPrimeFiniteDifferent318.local_zero_ideal b p j hj
  by_cases hz:FourRootAffineCoordinateRing318.coordinate b (some j)∈p
  · right
    exact he.trans (maximal_eq b hb j p hz hj).symm
  · left
    rw [he]
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_singleton _))
    exact IsLocalization.map_units (Stalk b p)
      ⟨FourRootAffineCoordinateRing318.coordinate b (some j),hz⟩
end FourRootAllPrimeZeroSimple318
