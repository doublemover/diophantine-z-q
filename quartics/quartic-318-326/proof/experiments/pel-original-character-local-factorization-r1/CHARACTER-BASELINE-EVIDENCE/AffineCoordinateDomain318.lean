module
public import AffineEquationFunctor318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace AffineCoordinateDomain318
open ShortAffineJacobian318 AffineEquationFunctor318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

@[expose] def model (A B:R) : WeierstrassCurve.Affine R := ⟨0,0,0,A,B⟩
abbrev CoordinateRing (A B:R) := (model A B).CoordinateRing
@[expose] def x (A B:R) : CoordinateRing A B := AdjoinRoot.of (model A B).polynomial Polynomial.X
@[expose] def y (A B:R) : CoordinateRing A B := AdjoinRoot.root (model A B).polynomial

lemma polynomial_formula (A B:R) : (model A B).polynomial=
    Polynomial.X^2-Polynomial.C (Polynomial.X^3+Polynomial.C A*Polynomial.X+Polynomial.C B) := by
  simp [WeierstrassCurve.Affine.polynomial,model]

lemma coordinate_relation (A B:R) : y A B^2-x A B^3-algebraMap R (CoordinateRing A B) A*x A B-
    algebraMap R (CoordinateRing A B) B=0 := by
  have h := AdjoinRoot.eval₂_root (model A B).polynomial
  conv at h => lhs; arg 3; rw [polynomial_formula]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,
    map_add,map_mul,map_pow] at h
  change y A B^2-(x A B^3+algebraMap R (CoordinateRing A B) A*x A B+
    algebraMap R (CoordinateRing A B) B)=0 at h
  linear_combination h

@[expose] def forward (A B:R) : Ring A B →ₐ[R] CoordinateRing A B :=
  toHom A B ⟨(x A B,y A B),coordinate_relation A B⟩
@[simp] theorem forward_x (A B:R) : forward A B (ShortAffineJacobian318.x A B)=x A B := toHom_x ..
@[simp] theorem forward_y (A B:R) : forward A B (ShortAffineJacobian318.y A B)=y A B := toHom_y ..

lemma eval_relation (A B:R) : (model A B).polynomial.eval₂
    (Polynomial.aeval (ShortAffineJacobian318.x A B)).toRingHom (ShortAffineJacobian318.y A B)=0 := by
  rw [polynomial_formula]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,
    map_add,map_mul,map_pow]
  have hx : (Polynomial.aeval (ShortAffineJacobian318.x A B)).toRingHom (Polynomial.X : Polynomial R) = ShortAffineJacobian318.x A B := Polynomial.aeval_X _
  have hc (c:R) : (Polynomial.aeval (ShortAffineJacobian318.x A B)).toRingHom (Polynomial.C c) = algebraMap R (Ring A B) c := Polynomial.aeval_C _ _
  rw [hx,hc,hc]
  change ShortAffineJacobian318.y A B^2-
    (ShortAffineJacobian318.x A B^3+algebraMap R (Ring A B) A*ShortAffineJacobian318.x A B+
    algebraMap R (Ring A B) B)=0
  linear_combination ShortAffineJacobian318.relation A B

@[expose] def backward (A B:R) : CoordinateRing A B →ₐ[R] Ring A B :=
  AdjoinRoot.liftAlgHom (model A B).polynomial (Polynomial.aeval (ShortAffineJacobian318.x A B))
    (ShortAffineJacobian318.y A B) (eval_relation A B)
@[simp] theorem backward_x (A B:R) : backward A B (x A B)=ShortAffineJacobian318.x A B := by
  rw [x,backward,AdjoinRoot.liftAlgHom_of,Polynomial.aeval_X]
@[simp] theorem backward_y (A B:R) : backward A B (y A B)=ShortAffineJacobian318.y A B := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem backward_forward (A B:R) : (backward A B).comp (forward A B)=AlgHom.id R _ := by
  apply AffineEquationFunctor318.hom_ext
  · simp
  · simp

theorem forward_backward (A B:R) : (forward A B).comp (backward A B)=AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change forward A B (backward A B (x A B))=x A B
    rw [backward_x,forward_x]
  · change forward A B (backward A B (y A B))=y A B
    rw [backward_y,forward_y]

/-- The literal multivariate quotient is the actual standard Weierstrass coordinate ring. -/
@[expose] def coordinateEquiv (A B:R) : Ring A B ≃ₐ[R] CoordinateRing A B :=
  AlgEquiv.ofAlgHom (forward A B) (backward A B) (forward_backward A B) (backward_forward A B)

/-- Integrality of the actual affine coordinate ring, without an irreducibility premise. -/
theorem affine_domain [IsDomain R] (A B:R) : IsDomain (Ring A B) :=
  (coordinateEquiv A B).injective.isDomain

end AffineCoordinateDomain318
