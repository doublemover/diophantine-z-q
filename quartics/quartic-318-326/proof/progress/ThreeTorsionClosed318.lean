module
public import ThreeTorsionScheme318
public section
noncomputable section
namespace ThreeTorsionClosed318
open CategoryTheory AlgebraicGeometry Polynomial ThreeTorsionAlgebra318 ThreeTorsionScheme318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma x_polynomial (f:R[X]) : aeval (x A B hD) f=
    algebraMap (XRing A B) (Ring A B hD)
      (AdjoinRoot.mk (ShortThreeTorsion318.polynomial A B) f) := by
  change aeval ((IsScalarTower.toAlgHom R (XRing A B) (Ring A B hD))
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))) f=_
  rw [Polynomial.aeval_algHom_apply,AdjoinRoot.aeval_eq]
  rfl

/-- Every element of the constructed torsion algebra is a polynomial in its
actual x and y coordinates; the elliptic-family coordinate map is surjective. -/
theorem coordinateMap_surjective : Function.Surjective (coordinateMap A B hD) := by
  intro z
  obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨a,ha⟩:=hf
    obtain ⟨b,hb⟩:=hg
    exact ⟨a+b,by rw [map_add,ha,hb,map_add]⟩
  | monomial n a =>
    obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective a
    refine ⟨aeval (ShortAffineJacobian318.x A B) f*(ShortAffineJacobian318.y A B)^n,?_⟩
    rw [map_mul,map_pow,←Polynomial.aeval_algHom_apply,coordinateMap_x,coordinateMap_y,
      x_polynomial,←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
      AdjoinRoot.mk_C,AdjoinRoot.mk_X]
    rfl

/-- The actual rank-eight relative torsion equation scheme is a closed
subscheme of the actual affine elliptic-family scheme. -/
theorem inclusion_closed : IsClosedImmersion (inclusion A B hD) :=
  IsClosedImmersion.spec_of_surjective _ (coordinateMap_surjective A B hD)

end ThreeTorsionClosed318
