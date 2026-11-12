module
public import FourRootCanonicalRationalEquations318
public import ActualLineRationalEquationOrders318
public import FourRootActualStalkDifferentialFrames318
public section
noncomputable section
namespace ActualOpenAffineDvr318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}} [IsIntegral X] {R:Type u} [CommRing R] [IsDomain R]
    (j:Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
    (p:PrimeSpectrum R) [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)]
/-- The original whole Scheme stalk is identified with the actual
localization at the SAME affine prime by the genuine open immersion
stalk map followed by Spec's canonical stalk isomorphism. -/
@[expose] def localEquivalence:
    X.presheaf.stalk (j p)≃+*Localization.AtPrime p.asIdeal:=
  ((asIso (j.stalkMap p)) ≪≫ Spec.stalkIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv
lemma actual_dvr:IsDiscreteValuationRing (X.presheaf.stalk (j p)):=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (localEquivalence j p).symm
end ActualOpenAffineDvr318

namespace FourRootActualSchemeDvr318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
abbrev A:=FourRootAffineCoordinateRing318.Ring b
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
@[expose] def finiteSpectrum(p:FinitePoints b):PrimeSpectrum (A b):=⟨finitePrime b p,finite_prime b p⟩
@[expose] def infinitySpectrum(p:InfinityPoints b):PrimeSpectrum (I b):=⟨infinityPrime b p,infinity_prime b p⟩
@[expose] def finiteImage(p:FinitePoints b):scheme b:=finiteChart b (finiteSpectrum b p)
@[expose] def infinityImage(p:InfinityPoints b):scheme b:=infinityChart b (infinitySpectrum b p)
local instance finitePrimeInstance(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
local instance infinityPrimeInstance(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
local instance finiteLocalizationDvr(p:FinitePoints b):
    IsDiscreteValuationRing (Localization.AtPrime (finitePrime b p)):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (A b)
    (FourRootLocalDifferentMultiplicity318.all_finite_prime_nonzero b hb p)
    (Localization.AtPrime (finitePrime b p))
@[expose] def finiteLocalEquivalence(p:FinitePoints b):
    (scheme b).presheaf.stalk (finiteImage b p)≃+*Localization.AtPrime (finitePrime b p):=
  ActualOpenAffineDvr318.localEquivalence (finiteChart b) (finiteSpectrum b p)
instance finiteActualDvr(p:FinitePoints b):
    IsDiscreteValuationRing ((scheme b).presheaf.stalk (finiteImage b p)):=
  ActualOpenAffineDvr318.actual_dvr (finiteChart b) (finiteSpectrum b p)
@[expose] def infinityLocalEquivalence(p:InfinityPoints b)(hp:p.val.1=0):
    (scheme b).presheaf.stalk (infinityImage b p)≃+*Localization.AtPrime (infinityPrime b p):=by
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  exact ActualOpenAffineDvr318.localEquivalence (infinityChart b) (infinitySpectrum b p)
lemma infinityActualDvr(p:InfinityPoints b)(hp:p.val.1=0):
    IsDiscreteValuationRing ((scheme b).presheaf.stalk (infinityImage b p)):=by
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  exact ActualOpenAffineDvr318.actual_dvr (infinityChart b) (infinitySpectrum b p)

/-- Actual intrinsic local-equation orders do not depend on which of
its genuine ambient canonical frames contains the original finite point. -/
theorem finite_equation_order_independent(p:FinitePoints b)(i j:Option (Fin 4))
    (hi:finiteImage b p∈FourRootActualCanonicalLine318.opens b hb i)
    (hj:finiteImage b p∈FourRootActualCanonicalLine318.opens b hb j):
    ActualDvrMeromorphicOrder318.order ((scheme b).presheaf.stalk (finiteImage b p))
      (scheme b).functionField (FourRootCanonicalRationalEquations318.localEquation b hb i)=
    ActualDvrMeromorphicOrder318.order ((scheme b).presheaf.stalk (finiteImage b p))
      (scheme b).functionField (FourRootCanonicalRationalEquations318.localEquation b hb j):=
  ActualLineRationalEquationOrders318.order_independent (FourRootIntrinsicCanonicalFrames318.omega b)
    (FourRootActualCanonicalLine318.opens b hb) (FourRootActualCanonicalLine318.frame b hb)
    (some 0) (FourRootCanonicalRationalEquations318.referenceCoefficient b hb) (finiteImage b p) i j hi hj
/-- All eight infinity evaluation centers use the original WHOLE Scheme
DVR. The regular-unit argument is valid even though dt has a pole there. -/
theorem infinity_equation_order_independent(p:InfinityPoints b)(hp:p.val.1=0)
    (i j:Option (Fin 4))
    (hi:infinityImage b p∈FourRootActualCanonicalLine318.opens b hb i)
    (hj:infinityImage b p∈FourRootActualCanonicalLine318.opens b hb j):
    letI:=infinityActualDvr b hb p hp
    ActualDvrMeromorphicOrder318.order ((scheme b).presheaf.stalk (infinityImage b p))
      (scheme b).functionField (FourRootCanonicalRationalEquations318.localEquation b hb i)=
    ActualDvrMeromorphicOrder318.order ((scheme b).presheaf.stalk (infinityImage b p))
      (scheme b).functionField (FourRootCanonicalRationalEquations318.localEquation b hb j):=by
  letI:=infinityActualDvr b hb p hp
  exact ActualLineRationalEquationOrders318.order_independent (FourRootIntrinsicCanonicalFrames318.omega b)
    (FourRootActualCanonicalLine318.opens b hb) (FourRootActualCanonicalLine318.frame b hb)
    (some 0) (FourRootCanonicalRationalEquations318.referenceCoefficient b hb) (infinityImage b p) i j hi hj
end FourRootActualSchemeDvr318
