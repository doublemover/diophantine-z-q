module
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import EvenContactEtale318
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public section
noncomputable section
namespace EtaleNormalization318
open TensorProduct
set_option maxHeartbeats 0
variable {R S K:Type*} [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual smooth-base-change integral-closure map has its entire image in
S itself, because the original integrally closed domain has no new integral
fraction-field elements. -/
theorem comparison_image (t:S⊗[R]integralClosure R K) :
    ∃s:S,algebraMap S (S⊗[R]K) s=
      (TensorProduct.toIntegralClosure R S K t:S⊗[R]K) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb =>
    obtain ⟨s,hs⟩:=ha
    obtain ⟨t,ht⟩:=hb
    exact ⟨s+t,by simp only [map_add,hs,ht,Subalgebra.coe_add]⟩
  | tmul s y =>
    obtain ⟨r,hr⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral y.property
    refine ⟨r • s,?_⟩
    change (r • s)⊗ₜ[R](1:K)=s⊗ₜ[R](y:K)
    rw [←hr,Algebra.algebraMap_eq_smul_one,smul_tmul]

/-- An actual smooth finite algebra over a normal domain is the integral closure
of that domain in its actual generic-fiber algebra. No normality or integral-
closure property of the smooth algebra is supplied. -/
theorem smooth_finite_integralClosure [Algebra.Smooth R S] [Module.Finite R S] :
    IsIntegralClosure S R (S⊗[R]K) := by
  constructor
  · exact Algebra.TensorProduct.includeLeft_injective (S:=S)
      (IsFractionRing.injective R K)
  · intro x
    constructor
    · intro hx
      have hxs:IsIntegral S x:=hx.tower_top
      obtain ⟨t,ht⟩:=(TensorProduct.toIntegralClosure_bijective_of_smooth
        (R:=R) (S:=S) (B:=K)).surjective ⟨x,hxs⟩
      obtain ⟨s,hs⟩:=comparison_image t
      refine ⟨s,?_⟩
      exact hs.trans (congrArg Subtype.val ht)
    · rintro ⟨s,rfl⟩
      exact (IsIntegral.of_finite R s).map (IsScalarTower.toAlgHom R S (S⊗[R]K))

/-- The constructed normalized even-contact root algebra is the actual integral
closure in its generic fiber, whether or not the unit is already a square. -/
theorem unit_root_integralClosure (u:Rˣ) (h2:IsUnit (2:R)) :
    IsIntegralClosure (EvenContactEtale318.RootRing u) R
      (EvenContactEtale318.RootRing u⊗[R]K) := by
  let:=EvenContactEtale318.rootRing_etale u h2
  let:=EvenContactEtale318.rootRing_finite u
  exact smooth_finite_integralClosure

/-- The same normalized cover is the integral closure of any actual finite
R-order acting compatibly on this generic fiber. This is the contact-order
normalization interface; its concrete generic-fiber presentation is separate. -/
theorem unit_root_integralClosure_over_order (u:Rˣ) (h2:IsUnit (2:R))
    (A:Type*) [CommRing A] [Algebra R A] [Module.Finite R A]
    [Algebra A (EvenContactEtale318.RootRing u⊗[R]K)]
    [IsScalarTower R A (EvenContactEtale318.RootRing u⊗[R]K)] :
    IsIntegralClosure (EvenContactEtale318.RootRing u) A
      (EvenContactEtale318.RootRing u⊗[R]K) := by
  let:=unit_root_integralClosure (K:=K) u h2
  exact IsIntegralClosure.tower_top (R:=R)

end EtaleNormalization318

namespace EvenContactDVRNormalization318
open TensorProduct
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual DVR specialization has no extra normality hypothesis. -/
theorem normalized_unit_cover (u:Rˣ) (h2:IsUnit (2:R)) :
    IsIntegralClosure (EvenContactEtale318.RootRing u) R
      (EvenContactEtale318.RootRing u⊗[R]FractionRing R) :=
  EtaleNormalization318.unit_root_integralClosure u h2

/-- In the DVR application, only the actual finite contact order and its
compatible generic-fiber algebra map remain to be instantiated. -/
theorem normalized_finite_order (u:Rˣ) (h2:IsUnit (2:R))
    (A:Type*) [CommRing A] [Algebra R A] [Module.Finite R A]
    [Algebra A (EvenContactEtale318.RootRing u⊗[R]FractionRing R)]
    [IsScalarTower R A (EvenContactEtale318.RootRing u⊗[R]FractionRing R)] :
    IsIntegralClosure (EvenContactEtale318.RootRing u) A
      (EvenContactEtale318.RootRing u⊗[R]FractionRing R) :=
  EtaleNormalization318.unit_root_integralClosure_over_order u h2 A

end EvenContactDVRNormalization318
