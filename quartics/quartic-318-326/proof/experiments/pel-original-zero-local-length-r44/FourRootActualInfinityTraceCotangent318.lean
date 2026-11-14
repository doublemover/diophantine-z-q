module
public import FourRootLocalDifferentMultiplicity318
public section
noncomputable section
namespace FourRootActualInfinityTraceCotangent318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualInfinityTraceTransport318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
abbrev Chart:=FourRootActualInfinityKaehler318.SourceRing b hb
local instance infinityBase:Algebra ℂ[X] (I b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance infinityFree:Module.Free ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance pointPrime(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
local instance chartBase:Algebra ℂ[X] (Chart b hb):=
  (Polynomial.aeval (FourRootActualInfinityKaehler318.reciprocalParameter b hb)).toAlgebra
/-- Actual relative differentials for the original reciprocal base v,
not intrinsic differentials for the rank-eight root coordinate u. -/
@[expose] def annihilator:Ideal (Chart b hb) where
  carrier:={a|∀ω:KaehlerDifferential ℂ[X] (Chart b hb),a • ω=0}
  zero_mem':=by intro ω;simp
  add_mem':=by intro a c ha hc ω;rw [add_smul,ha,hc,add_zero]
  smul_mem':=by intro r a ha ω;change (r*a) • ω=0;rw [mul_smul,ha,smul_zero]
lemma annihilator_eq:
    annihilator b hb=Ideal.span {FourRootActualInfinityKaehler318.coordinate b hb}:=by
  ext a
  exact FourRootActualRelativeCotangent318.infinity_simple_annihilator b hb a
@[expose] def chartToStalk(p:InfinityPoints b)(hp:p.val.1=0):Chart b hb→+*Stalk b p:=
  IsLocalization.Away.lift (FourRootActualInfinityKaehler318.denominator b hb)
    (IsLocalization.map_units (Stalk b p)
      ⟨FourRootActualInfinityKaehler318.denominator b hb,
        FourRootActualKaehlerNeighborhoods318.infinity_neighborhood b hb p hp⟩)
lemma coordinate_image(p:InfinityPoints b)(hp:p.val.1=0):
    chartToStalk b hb p hp (FourRootActualInfinityKaehler318.coordinate b hb)=uAt b p:=
  IsLocalization.Away.lift_eq _ _ _
/-- Direct equality of independently constructed original objects at
EVERY infinity center: the actual trace-dual different stalk equals the
mapped annihilator of the actual relative cotangent module over v=u². -/
theorem trace_equals_cotangent(p:InfinityPoints b)(hp:p.val.1=0):
    traceAt b hb p=(annihilator b hb).map (chartToStalk b hb p hp):=by
  rw [actual_infinity_trace b hb p hp,annihilator_eq,Ideal.map_span]
  simp only [Set.image_singleton,coordinate_image]
end FourRootActualInfinityTraceCotangent318
