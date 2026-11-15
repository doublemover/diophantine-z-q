module
public import DVRNormalizedContactPoint318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace DVRNormalizedFiniteOrder318
open Polynomial
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V]

/-- The whole finite contact order allows nonunit normalized twists.
No radicand or contact difference is inverted. -/
@[expose] def coefficient (d a : Fin 4 → V) (i : Fin 4) : V[X] :=
  C (d i)*(X-C (a i))
abbrev Order (d a : Fin 4 → V) := FourRootOrder318.Order (coefficient V d a)

theorem finite_free (d a : Fin 4 → V) :
    Module.Finite V[X] (Order V d a) ∧ Module.Free V[X] (Order V d a) :=
  FourRootOrder318.finite_free _

section Point
variable (d a : Fin 4 → V) (t : V) (z : Fin 4 → V)
  (hz : ∀ i,(z i)^2=d i*(t-a i))
local instance evaluationAlgebra : Algebra V[X] V := (Polynomial.evalRingHom t).toAlgebra

include hz in
theorem root_relation (i : Fin 4) :
    (z i)^2=algebraMap V[X] V (coefficient V d a i) := by
  simpa only [coefficient,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_C,Polynomial.eval_X] using hz i

@[expose] def pointMap : Order V d a →+* V :=
  (IntegralRootPointMaps318.fourMap (coefficient V d a) z
    (root_relation V d a t z hz)).toRingHom

theorem pointMap_polynomial (p : V[X]) :
    pointMap V d a t z hz (algebraMap V[X] (Order V d a) p)=Polynomial.eval t p :=
  (IntegralRootPointMaps318.fourMap _ _ (root_relation V d a t z hz)).commutes p

theorem pointMap_root (i : Fin 4) :
    pointMap V d a t z hz (FourRootOrderSigns318.generator (coefficient V d a) i)=z i :=
  IntegralRootPointMaps318.fourMap_generator _ _ _ i
end Point

variable [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]

/-- Actual integral finite models and points at EVERY coefficient place
where the original t is integral, including nonunit original twists. Each
normalized coefficient has exponent0 or1, and every original signed root is
recovered by its specified square multiplier. Normality, smoothness and
infinity at these excluded places are not asserted. -/
theorem exists_integral_model (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : V) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(algebraMap V K t-algebraMap V K (a i))) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K)
      (f : Order V (fun i => (u i:V)*pi^(e i:ℕ)) a →+* V),
      (∀ i,s i≠0) ∧
      (∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2) ∧
      (∀ p : V[X],f (algebraMap V[X] (Order V (fun i => (u i:V)*pi^(e i:ℕ)) a) p)=
        Polynomial.eval t p) ∧
      (∀ i,s i*algebraMap V K
        (f (FourRootOrderSigns318.generator (coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i) := by
  obtain ⟨u,e,s,z,hs,hc,hz,hz2,hyz⟩ :=
    DVRNormalizedContactPoint318.integral_roots V K pi hp c a t y hy
  refine ⟨u,e,s,pointMap V _ a t z hz2,hs,hc,pointMap_polynomial V _ a t z hz2,?_⟩
  intro i
  rw [pointMap_root]
  exact hyz i
end DVRNormalizedFiniteOrder318
