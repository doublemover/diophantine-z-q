module
public import FourRootActualSchemeDvr318
public import ActualDvrFractionValuationTransport318
public section
noncomputable section
namespace ActualOpenAffineStalkFraction318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}} [IsIntegral X] {R:Type u} [CommRing R] [IsDomain R]
    (j:Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j] (p:PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)]
abbrev Local:=X.presheaf.stalk (j p)
abbrev PrimeLocal:=Localization.AtPrime p.asIdeal
local instance actualDvr:IsDiscreteValuationRing (Local j p):=ActualOpenAffineDvr318.actual_dvr j p
local instance primeFieldAlgebra:Algebra (PrimeLocal p) (FractionRing R):=
  (ActualPrimeMeromorphicOrder318.embedding R p.asIdeal).toAlgebra
local instance sourceTower:IsScalarTower R (PrimeLocal p) (FractionRing R):=
  IsScalarTower.of_algebraMap_eq (fun x=>(IsLocalization.lift_eq _ x).symm)
local instance primeFraction:IsFractionRing (PrimeLocal p) (FractionRing R):=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl
    (PrimeLocal p) (FractionRing R)
/-- Extend the genuine original Scheme-stalk equivalence to its actual
fraction field. The target uses the SAME original affine fraction field
and SAME localization embedding as the explicit meromorphic dt orders. -/
@[expose] def comparison:X.functionField≃+*FractionRing R:=
  IsFractionRing.ringEquivOfRingEquiv (ActualOpenAffineDvr318.localEquivalence j p)
lemma on_stalk(s:Local j p):
    comparison j p (algebraMap (Local j p) X.functionField s)=
      ActualPrimeMeromorphicOrder318.embedding R p.asIdeal
        (ActualOpenAffineDvr318.localEquivalence j p s):=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ s
/-- Full actual section-germ compatibility at this point, not only a
relation between abstract isomorphic fraction fields. -/
lemma on_section(U:X.Opens)[Nonempty U](hx:j p∈U)(s:Γ(X,U)):
    comparison j p (X.germToFunctionField U s)=
      ActualPrimeMeromorphicOrder318.embedding R p.asIdeal
        (ActualOpenAffineDvr318.localEquivalence j p (X.presheaf.germ U (j p) hx s)):=by
  rw [←Scheme.algebraMap_germ_eq_germToFunctionField hx s,on_stalk]
/-- The normalized valuation of the ACTUAL Scheme local ring is exactly
the previously used normalized localization valuation under its true
coefficient-preserving fraction comparison, including poles and zero. -/
theorem value_preserved(f:X.functionField):
    ActualPrimeMeromorphicOrder318.value R p.asIdeal (comparison j p f)=
      ActualDvrMeromorphicOrder318.value (Local j p) X.functionField f:=
  ActualDvrFractionValuationTransport318.fraction_value
    (ActualOpenAffineDvr318.localEquivalence j p) (comparison j p).toRingHom
    (on_stalk j p) f
theorem order_preserved(f:X.functionField):
    ActualPrimeMeromorphicOrder318.order R p.asIdeal (comparison j p f)=
      ActualDvrMeromorphicOrder318.order (Local j p) X.functionField f:=by
  unfold ActualPrimeMeromorphicOrder318.order ActualDvrMeromorphicOrder318.order
  rw [value_preserved]
end ActualOpenAffineStalkFraction318
