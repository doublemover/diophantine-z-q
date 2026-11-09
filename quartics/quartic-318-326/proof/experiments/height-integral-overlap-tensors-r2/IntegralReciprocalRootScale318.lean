module
public import ThreeRootOrder318
public section
noncomputable section
namespace IntegralReciprocalRootScale318
open QuadraticPresentation318
open scoped TensorProduct
set_option maxHeartbeats 500000
variable {S : Type*} [CommRing S]

/-- Literal reciprocal-coordinate radicand identity, before division or
passage to a field. The original ramified unit is retained. -/
theorem parameter_identity (b k y u a v : S) (hk : b*k=1) (hu : y*u=b) :
    y^2 * (v*k*(1-a*k*u^2)) = v*(k*y^2-a) := by
  have h : (y*u*k)^2 = 1 := by rw [hu,hk,one_pow]
  calc
    _ = v*(k*y^2-a*(y*u*k)^2) := by ring
    _ = _ := by rw [h,mul_one]

/-- An explicit unit rescaling of the actual quadratic quotient.
The source root maps to y times the target root, preserving its sign. -/
@[expose] def rootEquiv (a b : S) (y : Sˣ) (ha : IsUnit a)
    (h : b = a*(y:S)^2) : RootRing b ≃ₐ[S] RootRing a :=
  (ContactGenericFiber318.rootParameterEquiv
    (h.trans (congrArg (fun z : S => z*(y:S)^2) ha.unit_spec.symm))).trans
    ((ContactGenericFiber318.scaleEquiv ha.unit (y:S) 1 y.isUnit).trans
      (ContactGenericFiber318.rootParameterEquiv ha.unit_spec))

@[simp] theorem rootEquiv_root (a b : S) (y : Sˣ) (ha : IsUnit a)
    (h : b = a*(y:S)^2) :
    rootEquiv a b y ha h (AdjoinRoot.root (polynomial b)) =
      algebraMap S (RootRing a) (y:S) * AdjoinRoot.root (polynomial a) := by
  simp only [rootEquiv,AlgEquiv.trans_apply,ContactGenericFiber318.rootParameterEquiv_generator,
    ContactGenericFiber318.scaleEquiv_generator,pow_one,map_mul,AlgEquiv.commutes]

/-- The actual three-root tensor order, with every original root rescaled
by the same genuine invertible branch coordinate. -/
@[expose] def orderEquiv (a b : Fin 3 → S) (y : Sˣ)
    (ha : ∀ j, IsUnit (a j)) (h : ∀ j, b j = a j*(y:S)^2) :
    ThreeRootOrder318.Order b ≃ₐ[S] ThreeRootOrder318.Order a :=
  Algebra.TensorProduct.congr (rootEquiv (a 0) (b 0) y (ha 0) (h 0))
    (Algebra.TensorProduct.congr (rootEquiv (a 1) (b 1) y (ha 1) (h 1))
      (rootEquiv (a 2) (b 2) y (ha 2) (h 2)))

/-- Equality of the actual three radicands transports their original tensor
presentation without choosing replacement generators. -/
@[expose] def orderParameterEquiv (a b : Fin 3 → S) (h : ∀ j, a j = b j) :
    ThreeRootOrder318.Order a ≃ₐ[S] ThreeRootOrder318.Order b :=
  Algebra.TensorProduct.congr (ContactGenericFiber318.rootParameterEquiv (h 0))
    (Algebra.TensorProduct.congr (ContactGenericFiber318.rootParameterEquiv (h 1))
      (ContactGenericFiber318.rootParameterEquiv (h 2)))

end IntegralReciprocalRootScale318
