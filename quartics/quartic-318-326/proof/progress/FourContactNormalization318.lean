module
public import FourContactOrder318
public import EtaleNormalization318
public section
noncomputable section
namespace FourContactNormalization318
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open scoped TensorProduct
open FourContactOrder318 FourUnitCover318
variable {R K:Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (u:Fin 4→Rˣ) (pi:R) (m:Fin 4→ℕ)

@[expose] def orderToGeneric : Order u pi m→ₐ[R]Cover u⊗[R]K :=
  Algebra.TensorProduct.includeLeft.comp (orderMap u pi m)
@[expose,instance_reducible] def orderAlgebra : Algebra (Order u pi m) (Cover u⊗[R]K) :=
  RingHom.toAlgebra (R:=Order u pi m) (S:=Cover u⊗[R]K) (orderToGeneric (K:=K) u pi m).toRingHom

theorem order_scalar_tower : letI:=orderAlgebra (K:=K) u pi m
    IsScalarTower R (Order u pi m) (Cover u⊗[R]K) := by
  letI:=orderAlgebra (K:=K) u pi m
  apply IsScalarTower.of_algebraMap_eq (R:=R) (S:=Order u pi m) (A:=Cover u⊗[R]K)
  intro r
  exact ((orderToGeneric (K:=K) u pi m).commutes r).symm

theorem orderToGeneric_injective (hpi:pi≠0) :
    Function.Injective (orderToGeneric (K:=K) u pi m) := by
  letI (i:Fin 4):Module.Free R (EvenContactEtale318.RootRing (u i)):=
    EvenContactEtale318.rootRing_free _
  exact (Algebra.TensorProduct.includeLeft_injective (S:=Cover u)
    (IsFractionRing.injective R K)).comp (orderMap_injective u pi m hpi)

/-- The generic-fiber equivalence is constructed from the four actual scaling
maps. The ambient algebra is allowed to split or to have repeated factors. -/
@[expose] def genericOrderEquiv (hpi:pi≠0) :
    K⊗[R]Order u pi m ≃ₐ[R] Cover u⊗[R]K :=
  ((genericEquiv u pi m (IsUnit.mk0 _
    (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hpi))).restrictScalars R).trans
      (Algebra.TensorProduct.comm R K (Cover u))

theorem genericOrderEquiv_on_order (hpi:pi≠0) (x:Order u pi m) :
    genericOrderEquiv (K:=K) u pi m hpi (1⊗ₜ[R]x)=orderToGeneric u pi m x := by
  simp only [genericOrderEquiv,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,
    genericEquiv_on_order,Algebra.TensorProduct.comm_tmul]
  rfl

/-- Actual integral closure of the joint four-contact order. No normality of
the cover, integral-closure assertion, or generic presentation is supplied. -/
theorem integralClosure [IsIntegrallyClosed R] (h2:IsUnit (2:R)) :
    letI:=orderAlgebra (K:=K) u pi m
    IsIntegralClosure (Cover u) (Order u pi m) (Cover u⊗[R]K) := by
  letI:=orderAlgebra (K:=K) u pi m
  letI:=order_scalar_tower (K:=K) u pi m
  letI:Module.Finite R (Order u pi m):=(finite_free u pi m).1
  letI:Module.Finite R (Cover u):=(finite_free_etale u h2).1
  letI:Algebra.Etale R (Cover u):=(finite_free_etale u h2).2.2
  letI:IsIntegralClosure (Cover u) R (Cover u⊗[R]K):=
    EtaleNormalization318.smooth_finite_integralClosure
  exact IsIntegralClosure.tower_top (R:=R)

/-- A normalized finite etale rank-sixteen cover of the actual rank-sixteen
joint raw order, over the original DVR. This includes all split branches. -/
theorem normalized_four_contacts [IsDiscreteValuationRing R]
    (h2:IsUnit (2:R)) (hpi:pi≠0) :
    letI:=orderAlgebra (K:=K) u pi m
    IsIntegralClosure (Cover u) (Order u pi m) (Cover u⊗[R]K) ∧
    Algebra.Etale R (Cover u) ∧ Module.Finite R (Cover u) ∧
    Module.finrank R (Cover u)=16 ∧ Module.finrank R (Order u pi m)=16 ∧
    Function.Injective (orderToGeneric (K:=K) u pi m) ∧
    ∃e:K⊗[R]Order u pi m ≃ₐ[R] Cover u⊗[R]K,
      ∀x,e (1⊗ₜ[R]x)=orderToGeneric u pi m x := by
  exact ⟨integralClosure u pi m h2,(finite_free_etale u h2).2.2,
    (finite_free_etale u h2).1,FourUnitCover318.rank_sixteen u,
    FourContactOrder318.rank_sixteen u pi m,orderToGeneric_injective u pi m hpi,
    genericOrderEquiv u pi m hpi,genericOrderEquiv_on_order u pi m hpi⟩
end FourContactNormalization318
