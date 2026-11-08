module
public import SourceBranchFullInertia318
public import SourceGlobalAffine318
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public section
noncomputable section
namespace SourceBranchValuation318
open ContactKummerOrder318 Polynomial IsDedekindDomain
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceDomain:IsDomain (SourceOrder c):=source_domain c
local instance sourceFinite:Module.Finite R (SourceOrder c):=(source_finite_free c).1
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c

/-- The whole original four-contact order is Dedekind; its polynomial
base and exact whole-source normality are retained. -/
theorem source_dedekind:IsDedekindDomain (SourceOrder c):=by
  letI:=SourceGlobalAffine318.source_integrallyClosed c
  letI:IsNoetherianRing (SourceOrder c):=IsNoetherianRing.of_finite R (SourceOrder c)
  letI:Algebra.IsIntegral R (SourceOrder c):=Algebra.IsIntegral.of_finite R (SourceOrder c)
  letI:Ring.DimensionLEOne (SourceOrder c):=Ring.DimensionLEOne.of_isIntegral R (SourceOrder c)
  exact { (inferInstance:IsDomain (SourceOrder c)),
    (inferInstance:IsNoetherianRing (SourceOrder c)),
    (inferInstance:Ring.DimensionLEOne (SourceOrder c)),
    (inferInstance:IsIntegrallyClosed (SourceOrder c)) with }
local instance sourceDedekind:IsDedekindDomain (SourceOrder c):=source_dedekind c

lemma polynomial_injective:Function.Injective (algebraMap R (SourceOrder c)):=by
  intro x y h
  apply IsFractionRing.injective R K
  apply RingHom.injective (algebraMap K (L c))
  simpa only [←SourceFractionField318.embedding_on_polynomial] using congrArg (embedding c) h

variable {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F) (i:Fin 4)
    (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
local instance kernelPrime:(SourceBranchResidueInertia318.prime c p).IsPrime:=
  SourceBranchResidueInertia318.prime_isPrime c p
include ht
lemma prime_ne_bot:SourceBranchResidueInertia318.prime c p≠⊥:=by
  intro h
  have hm:algebraMap R (SourceOrder c) (X-C (LinearContactSquareclass318.contacts i))∈
      SourceBranchResidueInertia318.prime c p:=by
    change p (algebraMap R (SourceOrder c) (X-C (LinearContactSquareclass318.contacts i)))=0
    rw [p.commutes,map_sub,ht]
    change algebraMap ℚ F (LinearContactSquareclass318.contacts i)-
      algebraMap R F (algebraMap ℚ R (LinearContactSquareclass318.contacts i))=0
    rw [←IsScalarTower.algebraMap_apply ℚ R F]
    exact sub_self _
  rw [h,Ideal.mem_bot] at hm
  exact Polynomial.X_sub_C_ne_zero _ ((polynomial_injective c) (by simpa only [map_zero] using hm))

/-- The actual kernel prime, not a chosen replacement prime. -/
@[expose] def place:HeightOneSpectrum (SourceOrder c):=
  ⟨SourceBranchResidueInertia318.prime c p,SourceBranchResidueInertia318.prime_isPrime c p,
    prime_ne_bot c p i ht⟩
@[simp] theorem place_ideal:(place c p i ht).asIdeal=SourceBranchResidueInertia318.prime c p:=rfl
/-- The localization valuation subring inside the specified original
whole function field, with its original source-order embedding. -/
@[expose] abbrev valuationRing:ValuationSubring (L c):=
  HeightOneSpectrum.valuationSubringAtPrime (L c) (place c p i ht)

theorem actual_localization:IsLocalization
    (SourceBranchResidueInertia318.prime c p).primeCompl (valuationRing c p i ht):=by
  change IsLocalization (place c p i ht).asIdeal.primeCompl
    (HeightOneSpectrum.valuationSubringAtPrime (L c) (place c p i ht))
  infer_instance

theorem equals_adic_valuation:valuationRing c p i ht=
    ((place c p i ht).valuation (L c)).valuationSubring:=
  HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (place c p i ht)
end SourceBranchValuation318
