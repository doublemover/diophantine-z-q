module
public import FourRootActualOrderGalois318
public import FourRootInfinitySmooth318
public import FourRootSquaredInfinityBase318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public section
noncomputable section
namespace FourRootActualDedekind318
open FourRootActualGenericField318 FourRootAffineTensorPresentation318 FourRootActualFractionField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance rawAlgebra:Algebra (A b) (L b):=(affineEmbedding b).toAlgebra
local instance baseAlgebra:Algebra P (L b):=
  ((algebraMap K (L b)).comp (algebraMap P K)).toAlgebra
local instance baseTower:IsScalarTower P K (L b):=
  IsScalarTower.of_algebraMap_eq (fun _=>rfl)
local instance affineTower:IsScalarTower P (A b) (L b):=
  IsScalarTower.of_algebraMap_eq (fun p=>(embedding_on_polynomial b p).symm)
local instance affineClosure:IsIntegralClosure (A b) P (L b):=
  FourRootActualOrderGalois318.integralClosure b hb
local instance rawFinite:FiniteDimensional K (L b):=
  Module.finite_of_finrank_pos (by rw [actual_degree b hb];decide)
local instance actualGalois:IsGalois K (L b):=ActualKummerGalois318.raw_galois (parameter b)
/-- The SAME whole finite coordinate ring is Dedekind, through its
constructed entire integral-closure identification in the original field. -/
theorem finite_dedekind:IsDedekindDomain (A b):=
  IsIntegralClosure.isDedekindDomain P K (L b) (A b)
/-- The whole infinity ring is Dedekind over the ACTUAL reciprocal
projective base v=u². Its rank-eight u-presentation is not used here. -/
theorem infinity_dedekind:IsDedekindDomain (FourRootInfinityCoordinateRing318.Ring b):=by
  let I:=FourRootInfinityCoordinateRing318.Ring b
  letI:Algebra P I:=(Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
  letI:IsDomain I:=FourRootInfinityDomain318.infinity_domain b hb
  letI:Module.Finite P I:=(FourRootSquaredInfinityBase318.finite_free b).1
  letI:IsIntegrallyClosed I:=FourRootInfinitySmooth318.integrallyClosed b hb
  letI:IsNoetherianRing I:=IsNoetherianRing.of_finite P I
  letI:Algebra.IsIntegral P I:=Algebra.IsIntegral.of_finite P I
  letI:Ring.DimensionLEOne I:=Ring.DimensionLEOne.of_isIntegral P I
  exact { (inferInstance:IsDomain I), (inferInstance:IsNoetherianRing I),
    (inferInstance:Ring.DimensionLEOne I), (inferInstance:IsIntegrallyClosed I) with }
end FourRootActualDedekind318
