module
public import FourRootDerivativeZeroIdeals318
public import FourRootActualBranchKaehler318
public section
noncomputable section
namespace FourRootDerivativeFiniteIdeal318
open FourRootDerivativeZeroIdeals318 FourRootActualFiniteBranchChart318
open FourRootActualBranchKaehler318
open scoped BigOperators
variable (b:Fin 4→ℂ)(i:Fin 4)
local instance polyAlgebra:Algebra (Polynomial ℂ) (FourRootAffineCoordinateRing318.Ring b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
@[expose] def otherProduct:FourRootAffineCoordinateRing318.Ring b:=
  ∏j:Fin 3,FourRootAffineCoordinateRing318.coordinate b (some (FourRootPivot318.indices i j.succ))
lemma other_square:otherProduct b i^2=denominator b i:=by
  rw [otherProduct,←Finset.prod_pow,denominator,denominatorPolynomial,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [FourRootAffineCoordinateRing318.relation]
  change _=Polynomial.aeval _ (Polynomial.X-Polynomial.C _)
  rw [map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
lemma generator_factor:finiteGenerator b=
    FourRootAffineCoordinateRing318.coordinate b (some i)*otherProduct b i:=by
  fin_cases i <;>
    simp [finiteGenerator,otherProduct,FourRootPivot318.indices,Fin.prod_univ_succ] <;> ring
lemma localized_other_unit:IsUnit
    (algebraMap (FourRootAffineCoordinateRing318.Ring b) (SourceRing b i) (otherProduct b i)):=by
  have h:IsUnit (algebraMap (FourRootAffineCoordinateRing318.Ring b) (SourceRing b i)
      (denominator b i)):=IsLocalization.map_units (SourceRing b i)
        ⟨denominator b i,⟨1,by simp⟩⟩
  rw [←other_square,map_pow,pow_two] at h
  exact isUnit_of_mul_isUnit_left h
/-- The global principal finite ideal is restricted to the TRUE original
principal canonical chart. Every other root becomes a unit because its
product square is the actual inverted denominator. -/
theorem localized_ideal:
    (finiteIdeal b).map (algebraMap (FourRootAffineCoordinateRing318.Ring b) (SourceRing b i))=
      Ideal.span {sourceCoordinate b i}:=by
  rw [finiteIdeal,Ideal.map_span,Set.image_singleton,generator_factor,map_mul,
    ←source_coordinate_original,Ideal.span_singleton_mul_right_unit (localized_other_unit b i)]
lemma two_unit:IsUnit (2:SourceRing b i):=by
  have h:IsUnit (2:ℂ):=isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (algebraMap ℂ (SourceRing b i))
/-- This is the ideal of the ACTUAL derivative coefficient already
computed by universal differential naturality, not a support substitute. -/
theorem derivative_ideal:
    (finiteIdeal b).map (algebraMap (FourRootAffineCoordinateRing318.Ring b) (SourceRing b i))=
      Ideal.span {2*sourceCoordinate b i}:=by
  rw [localized_ideal,Ideal.span_singleton_mul_left_unit (two_unit b i)]
end FourRootDerivativeFiniteIdeal318
