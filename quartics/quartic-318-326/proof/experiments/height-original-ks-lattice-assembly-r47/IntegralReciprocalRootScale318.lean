module
public import ThreeRootOrder318
public section
noncomputable section
namespace IntegralReciprocalRootScale318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [CommRing S]

/-- Literal reciprocal-coordinate radicand identity, before division or
passage to a field. The original ramified unit is retained. -/
theorem parameter_identity (b k y u a v : S) (hk : b*k=1) (hu : y*u=b) :
    y^2 * (v*k*(1-a*k*u^2)) = v*(k*y^2-a) := by
  have h : (y*u*k)^2 = 1 := by rw [hu,hk,one_pow]
  calc
    _ = v*(k*y^2-a*(y*u*k)^2) := by ring
    _ = _ := by rw [h,mul_one]

/-- Scaling the ROOT by a unit does not require the radicand to be a unit.
This map therefore retains the branch points omitted by an etale-only chart. -/
@[expose] def rootForward (a b : S) (y : Sˣ) (h : b=a*(y:S)^2) :
    RootRing b →ₐ[S] RootRing a :=
  AdjoinRoot.liftAlgHom (polynomial b) (Algebra.ofId S _)
    (algebraMap S (RootRing a) (y:S) * AdjoinRoot.root (polynomial a)) (by
      change Polynomial.aeval _ (X^2-C b)=0
      rw [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,mul_pow,root_square,
        ←map_pow,←map_mul]
      apply sub_eq_zero.mpr
      congr 1
      rw [h]
      ring)

@[simp] theorem rootForward_root (a b : S) (y : Sˣ) (h : b=a*(y:S)^2) :
    rootForward a b y h (AdjoinRoot.root (polynomial b))=
      algebraMap S (RootRing a) (y:S)*AdjoinRoot.root (polynomial a) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem rootInverse_parameter (a b : S) (y : Sˣ) (h : b=a*(y:S)^2) :
    a=b*(↑y⁻¹:S)^2 := by
  rw [h,mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one]

/-- A genuine two-sided equivalence of the full quadratic orders, even over
nonreduced bases and at zero radicands. The original root sign is fixed. -/
@[expose] def directRootEquiv (a b : S) (y : Sˣ) (h : b=a*(y:S)^2) :
    RootRing b ≃ₐ[S] RootRing a :=
  AlgEquiv.ofAlgHom (rootForward a b y h)
    (rootForward b a y⁻¹ (rootInverse_parameter a b y h))
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply,rootForward_root,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul])
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply,rootForward_root,map_mul,AlgHom.commutes,AlgHom.id_apply]
      rw [←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul])

@[simp] theorem directRootEquiv_root (a b : S) (y : Sˣ) (h : b=a*(y:S)^2) :
    directRootEquiv a b y h (AdjoinRoot.root (polynomial b))=
      algebraMap S (RootRing a) (y:S)*AdjoinRoot.root (polynomial a) :=
  rootForward_root a b y h

/-- Normalize the target carrier before applying any outer algebra map.
The two polynomial quotient presentations have the same explicit equation,
but their ring structures must not be left implicit in a nested rewrite. -/
theorem scale_root_in_original_carrier (u : Sˣ) (y : Sˣ) :
    ContactGenericFiber318.scaleEquiv u (y:S) 1 y.isUnit
      (AdjoinRoot.root (polynomial ((u:S)*(y:S)^(2*1)))) =
      algebraMap S (RootRing (u:S)) (y:S) * AdjoinRoot.root (polynomial (u:S)) := by
  simpa only [pow_one,EvenContactEtale318.RootRing,EvenContactEtale318.root,
    EvenContactEtale318.polynomial,QuadraticPresentation318.RootRing,polynomial] using
      ContactGenericFiber318.scaleEquiv_generator u (y:S) 1 y.isUnit

/-- The original interface, now implemented directly in its single literal
quadratic carrier. The unit-radicand hypothesis remains explicit for existing
consumers; the two-sided root-scaled maps themselves need only the unit y. -/
@[expose] def rootEquiv (a b : S) (y : Sˣ) (ha : IsUnit a)
    (h : b = a*(y:S)^2) : RootRing b ≃ₐ[S] RootRing a :=
  directRootEquiv a b y h

@[simp] theorem rootEquiv_root (a b : S) (y : Sˣ) (ha : IsUnit a)
    (h : b = a*(y:S)^2) :
    rootEquiv a b y ha h (AdjoinRoot.root (polynomial b)) =
      algebraMap S (RootRing a) (y:S) * AdjoinRoot.root (polynomial a) :=
  rootForward_root a b y h

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
