module
public import ContactOrder318
public import EtaleNormalization318
public section
noncomputable section
namespace NormalizedContactOrder318
set_option maxHeartbeats 800000
open scoped TensorProduct
open QuadraticPresentation318 ContactBaseChange318 ContactGenericFiber318 ContactOrder318
variable {R K:Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

@[expose] def orderToGeneric (u:Rˣ) (pi:R) (m:ℕ) :
    RootRing ((u:R)*pi^(2*m)) →ₐ[R] (EvenContactEtale318.RootRing u ⊗[R] K) :=
  Algebra.TensorProduct.includeLeft.comp (contactMap u pi m)

@[expose, instance_reducible] def orderAlgebra (u:Rˣ) (pi:R) (m:ℕ) :
    Algebra (RootRing ((u:R)*pi^(2*m))) (EvenContactEtale318.RootRing u ⊗[R] K) :=
  (orderToGeneric (K:=K) u pi m).toRingHom.toAlgebra

theorem order_scalar_tower (u:Rˣ) (pi:R) (m:ℕ) :
    letI:=orderAlgebra (K:=K) u pi m
    IsScalarTower R (RootRing ((u:R)*pi^(2*m))) (EvenContactEtale318.RootRing u ⊗[R] K) := by
  letI:=orderAlgebra (K:=K) u pi m
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((orderToGeneric (K:=K) u pi m).commutes r).symm

theorem orderToGeneric_injective (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) :
    Function.Injective (orderToGeneric (K:=K) u pi m) := by
  letI:=EvenContactEtale318.rootRing_free u
  exact (Algebra.TensorProduct.includeLeft_injective (S:=EvenContactEtale318.RootRing u)
    (IsFractionRing.injective R K)).comp (contactMap_injective u pi m hp)

/-- The concrete contact order has the constructed unit-root cover as its
actual integral closure in the generic fiber. Normality is derived from the
normal base and actual etaleness, not assumed for the root cover. -/
theorem integralClosure [IsIntegrallyClosed R] (u:Rˣ) (pi:R) (m:ℕ) (h2:IsUnit (2:R)) :
    letI:=orderAlgebra (K:=K) u pi m
    IsIntegralClosure (EvenContactEtale318.RootRing u) (RootRing ((u:R)*pi^(2*m)))
      (EvenContactEtale318.RootRing u ⊗[R] K) := by
  letI:=orderAlgebra (K:=K) u pi m
  letI:=order_scalar_tower (K:=K) u pi m
  letI:=finite_order u pi m
  exact EtaleNormalization318.unit_root_integralClosure_over_order u h2 _

/-- A genuine generic-fiber algebra equivalence, compatible with the concrete
order map. No total-quotient-domain claim is made for a possibly split algebra. -/
@[expose] def genericOrderEquiv (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) :
    K ⊗[R] RootRing ((u:R)*pi^(2*m)) ≃ₐ[R]
      EvenContactEtale318.RootRing u ⊗[R] K :=
  ((genericFiberEquiv u pi m (IsUnit.mk0 _
    (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hp))).restrictScalars R).trans
      (Algebra.TensorProduct.comm R K (EvenContactEtale318.RootRing u))

theorem genericOrderEquiv_on_order (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0)
    (x:RootRing ((u:R)*pi^(2*m))) :
    genericOrderEquiv (K:=K) u pi m hp (1 ⊗ₜ[R] x)=orderToGeneric u pi m x := by
  simp only [genericOrderEquiv,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,
    genericFiberEquiv_on_order,Algebra.TensorProduct.comm_tmul]
  rfl

/-- The concrete even-contact normalization over an actual DVR is finite etale,
with an injective order map and a compatible genuine generic-fiber isomorphism. -/
theorem normalized_even_contact [IsDiscreteValuationRing R]
    (u:Rˣ) (pi:R) (m:ℕ) (h2:IsUnit (2:R)) (hp:pi≠0) :
    letI:=orderAlgebra (K:=K) u pi m
    IsIntegralClosure (EvenContactEtale318.RootRing u) (RootRing ((u:R)*pi^(2*m)))
      (EvenContactEtale318.RootRing u ⊗[R] K) ∧
    Algebra.Etale R (EvenContactEtale318.RootRing u) ∧
    Module.Finite R (EvenContactEtale318.RootRing u) ∧
    Function.Injective (orderToGeneric (K:=K) u pi m) ∧
    Nonempty (K ⊗[R] RootRing ((u:R)*pi^(2*m)) ≃ₐ[R]
      EvenContactEtale318.RootRing u ⊗[R] K) := by
  exact ⟨integralClosure u pi m h2,EvenContactEtale318.rootRing_etale u h2,
    EvenContactEtale318.rootRing_finite u,orderToGeneric_injective u pi m hp,
    ⟨genericOrderEquiv u pi m hp⟩⟩

end NormalizedContactOrder318
