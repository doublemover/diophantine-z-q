module
public import FourRootOrder318
public import Mathlib.RingTheory.Etale.Field
public section
noncomputable section
namespace FourRootGenericReduced318
open scoped TensorProduct
variable {R : Type*} [CommRing R] [IsDomain R] (a : Fin 4 → R)

/-- Repeated nonzero radicands are permitted. The generic algebra is
etale and reduced, not necessarily a field or even a domain. -/
theorem reduced (h2 : (2 : R) ≠ 0) (ha : ∀ i, a i ≠ 0) :
    IsReduced (FourRootOrder318.Order a) := by
  let K := FractionRing R
  have hi : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let b : Fin 4 → K := fun i => algebraMap R K (a i)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply hi
    simpa only [map_ofNat, map_zero] using h
  letI : Algebra.Etale K (FourRootOrder318.Order b) :=
    FourRootOrder318.etale b (isUnit_iff_ne_zero.mpr h2K)
      (fun i => isUnit_iff_ne_zero.mpr (fun h => ha i (hi (by simpa only [b, map_zero] using h))))
  letI : IsReduced (FourRootOrder318.Order b) :=
    Algebra.FormallyUnramified.isReduced_of_field K (FourRootOrder318.Order b)
  letI : Module.Free R (FourRootOrder318.Order a) := (FourRootOrder318.finite_free a).2
  let e := FourRootOrder318.baseChange a K
  let f : FourRootOrder318.Order a →+* FourRootOrder318.Order b :=
    e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : FourRootOrder318.Order a →ₐ[R]
        K ⊗[R] FourRootOrder318.Order a).toRingHom
  have hf : Function.Injective f := e.injective.comp
    (Algebra.TensorProduct.includeRight_injective
      (R := R) (A := K) (B := FourRootOrder318.Order a) hi)
  exact isReduced_of_injective f hf

end FourRootGenericReduced318
