module
public import DVRNormalizedFiniteOrder318
public section
noncomputable section
namespace DVRNormalizedInfinityOrder318
open Polynomial
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V]

/-- The original reciprocal coordinate is w=1/t. Multiplying each original
root by w gives this whole integral infinity equation, even for nonunit twists.
All four roots are retained and no discriminant or radicand is inverted. -/
@[expose] def coefficient (d a : Fin 4 → V) (i : Fin 4) : V[X] :=
  C (d i)*X*(1-C (a i)*X)
abbrev Order (d a : Fin 4 → V) := FourRootOrder318.Order (coefficient V d a)

theorem finite_free (d a : Fin 4 → V) :
    Module.Finite V[X] (Order V d a) ∧ Module.Free V[X] (Order V d a) :=
  FourRootOrder318.finite_free _

section Point
variable (d a : Fin 4 → V) (w : V) (z : Fin 4 → V)
  (hz : ∀ i,(z i)^2=d i*w*(1-a i*w))
local instance evaluationAlgebra : Algebra V[X] V := (Polynomial.evalRingHom w).toAlgebra
include hz in
theorem root_relation (i : Fin 4) :
    (z i)^2=algebraMap V[X] V (coefficient V d a i) := by
  simpa only [coefficient,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X] using hz i
@[expose] def pointMap : Order V d a →+* V :=
  (IntegralRootPointMaps318.fourMap _ z (root_relation V d a w z hz)).toRingHom

theorem pointMap_polynomial (p : V[X]) :
    pointMap V d a w z hz (algebraMap V[X] (Order V d a) p)=Polynomial.eval w p :=
  (IntegralRootPointMaps318.fourMap _ z (root_relation V d a w z hz)).commutes p

theorem pointMap_root (i : Fin 4) :
    pointMap V d a w z hz (FourRootOrderSigns318.generator (coefficient V d a) i)=z i :=
  IntegralRootPointMaps318.fourMap_generator _ _ _ i
end Point

section Field
variable {K : Type*} [Field K]
theorem reciprocal_root (c d s t a y : K) (hs : s≠0) (ht : t≠0)
    (hc : c=d*s^2) (hy : y^2=c*(t-a)) :
    (y/(s*t))^2=d*t⁻¹*(1-a*t⁻¹) := by
  rw [div_pow,hy,hc]
  field_simp [hs,ht]
  <;> ring

theorem original_root (s t y : K) (hs : s≠0) (ht : t≠0) :
    s*t*(y/(s*t))=y := by
  field_simp [hs,ht]
end Field

variable [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]

/-- The actual original signed infinity roots descend into the same DVR.
The only scalar division is by the specified nonzero square factor and t;
no original twist is required to be a unit. -/
theorem integral_roots (d a : Fin 4 → V) (c : Fin 4 → Kˣ)
    (s : Fin 4 → K) (hs : ∀ i,s i≠0)
    (hc : ∀ i,(c i:K)=algebraMap V K (d i)*(s i)^2)
    (t : K) (ht : t≠0) (w : V) (hw : algebraMap V K w=t⁻¹)
    (y : Fin 4 → K) (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i))) :
    ∃ z : Fin 4 → V,
      (∀ i,algebraMap V K (z i)=y i/(s i*t)) ∧
      (∀ i,(z i)^2=d i*w*(1-a i*w)) ∧
      (∀ i,s i*t*algebraMap V K (z i)=y i) := by
  have h (i : Fin 4) : ∃ z : V,algebraMap V K z=y i/(s i*t) ∧
      z^2=d i*w*(1-a i*w) := by
    apply IntegralValuativeRootCoordinates318.square_preimage V K
    rw [map_mul,map_mul,map_sub,map_one,map_mul,hw]
    exact reciprocal_root _ _ _ _ _ _ (hs i) ht (hc i) (hy i)
  choose z hz hz2 using h
  refine ⟨z,hz,hz2,?_⟩
  intro i
  rw [hz]
  exact original_root _ _ _ (hs i) ht
end DVRNormalizedInfinityOrder318
