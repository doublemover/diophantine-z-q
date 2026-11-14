module
public import FourRootDerivativeIdealClosed318
public import FourRootDerivativeInfinityIdeal318
public import FourRootInfinityDomain318
public section
noncomputable section
namespace FourRootDerivativeIdealRegular318
open FourRootDerivativeZeroIdeals318
open scoped BigOperators
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance finiteDomain:IsDomain (FourRootAffineCoordinateRing318.Ring b):=
  FourRootActualGenericField318.affine_domain b hb
local instance infinityDomain:IsDomain (FourRootInfinityCoordinateRing318.Ring b):=
  FourRootInfinityDomain318.infinity_domain b hb
lemma finite_nonzero:finiteGenerator b≠0:=by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact FourRootInfinityDomain318.finite_root_ne_zero b hb i
lemma infinity_image:
    FourRootInfinityAffineComparison318.equivalence b hb (infinityGenerator b)=
      algebraMap ℂ (FourRootAffineCoordinateRing318.Ring (FourRootReciprocalBranchData318.branches b))
        (FourRootDerivativeInfinityIdeal318.scaleProduct b)*
          finiteGenerator (FourRootReciprocalBranchData318.branches b):=by
  change FourRootInfinityAffineComparison318.equivalence b hb
    (FourRootInfinityCoordinateRing318.coordinate b none*
      FourRootDerivativeInfinityIdeal318.ratioProduct b)=_
  rw [map_mul,FourRootDerivativeInfinityIdeal318.ratio_image]
  change FourRootAffineCoordinateRing318.coordinate _ (some 0)*(_*_) = _
  rw [FourRootDerivativeFiniteIdeal318.generator_factor _ 0]
  ring
lemma infinity_nonzero:infinityGenerator b≠0:=by
  intro h
  have he:=congrArg (FourRootInfinityAffineComparison318.equivalence b hb) h
  rw [infinity_image,map_zero] at he
  letI:IsDomain (FourRootAffineCoordinateRing318.Ring (FourRootReciprocalBranchData318.branches b)):=
    FourRootActualGenericField318.affine_domain _ (FourRootReciprocalBranchData318.branches_injective b hb)
  have hc:algebraMap ℂ (FourRootAffineCoordinateRing318.Ring (FourRootReciprocalBranchData318.branches b))
      (FourRootDerivativeInfinityIdeal318.scaleProduct b)≠0:=
    ((isUnit_iff_ne_zero.mpr (FourRootDerivativeInfinityIdeal318.scaleProduct_ne b hb)).map
      (algebraMap ℂ _)).ne_zero
  exact mul_ne_zero hc
    (finite_nonzero _ (FourRootReciprocalBranchData318.branches_injective b hb)) he
/-- The literal equations defining the ACTUAL global closed subscheme
are regular on the two genuine covering affine charts. Combined with
the already proved quotient Cartesian squares this is the effective
principal Cartier criterion, not a radical/support-only zero locus. -/
theorem finite_regular:finiteGenerator b∈nonZeroDivisors (FourRootAffineCoordinateRing318.Ring b):=
  mem_nonZeroDivisors_iff_ne_zero.mpr (finite_nonzero b hb)
theorem infinity_regular:infinityGenerator b∈nonZeroDivisors (FourRootInfinityCoordinateRing318.Ring b):=
  mem_nonZeroDivisors_iff_ne_zero.mpr (infinity_nonzero b hb)
end FourRootDerivativeIdealRegular318
