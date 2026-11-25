module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace OpenJModel318
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

@[expose] def curve (j v : R) : WeierstrassCurve R :=
  ⟨0,0,0,-3*j*v,-2*j*v⟩

/-- The literal short Weierstrass equation, over a ring rather than only a field. -/
theorem discriminant (j v : R) (hv : (j-1728)*v=1) :
    (curve j v).Δ=1728^2*j^2*v^3 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination 1728*j^2*v^2*hv

theorem c4 (j v : R) : (curve j v).c₄=144*j*v := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem c4_cube (j v : R) (hv : (j-1728)*v=1) :
    (curve j v).c₄^3=j*(curve j v).Δ := by
  rw [c4,discriminant j v hv]
  ring

theorem discriminant_unit (j v : R) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R))
    (hj : IsUnit j) (hv : (j-1728)*v=1) : IsUnit (curve j v).Δ := by
  rw [discriminant j v hv]
  have hc : IsUnit (1728:R) := by
    convert (h2.pow 6).mul (h3.pow 3) using 1; norm_num
  have hunitv : IsUnit v := IsUnit.of_mul_eq_one_right _ hv
  exact ((hc.pow 2).mul (hj.pow 2)).mul (hunitv.pow 3)

theorem j_invariant (j v : R) (hv : (j-1728)*v=1) [(curve j v).IsElliptic] :
    (curve j v).j=j := by
  rw [WeierstrassCurve.j, c4_cube j v hv]
  rw [mul_comm j, ←mul_assoc]
  exact (congrArg (fun z : R => z*j) (curve j v).isUnit_Δ.val_inv_mul).trans (one_mul j)

/-- This is exactly the affine coordinate ring of
Spec Z[1/(6N),j,1/(j(j-1728))]. -/
@[expose] def denominator (N : ℕ) : Polynomial ℤ :=
  (6*(N:Polynomial ℤ))*Polynomial.X*(Polynomial.X-1728)
abbrev Base (N : ℕ) := Localization.Away (denominator N)
@[expose] def jCoord (N : ℕ) : Base N := algebraMap (Polynomial ℤ) (Base N) Polynomial.X

theorem base_units (N : ℕ) : IsUnit (2:Base N) ∧ IsUnit (3:Base N) ∧
    IsUnit (N:Base N) ∧ IsUnit (jCoord N) ∧ IsUnit (jCoord N-1728) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S:=Base N) (denominator N)
  simp only [denominator, map_mul, map_sub, map_natCast, map_ofNat, jCoord, IsUnit.mul_iff] at h ⊢
  have hsix : IsUnit (2:Base N) ∧ IsUnit (3:Base N) := by
    simpa only [show (6:Base N)=2*3 by norm_num, IsUnit.mul_iff] using h.1.1.1
  exact ⟨hsix.1,hsix.2,h.1.1.2,h.1.2,h.2⟩

@[expose] def denominatorUnit (N : ℕ) : (Base N)ˣ := (base_units N).2.2.2.2.unit
@[expose] def inverseDenominator (N : ℕ) : Base N := ↑(denominatorUnit N)⁻¹
@[expose] def integralModel (N : ℕ) : WeierstrassCurve (Base N) :=
  curve (jCoord N) (inverseDenominator N)

theorem denominator_inverse (N : ℕ) :
    (jCoord N-1728)*inverseDenominator N=1 := by
  exact (base_units N).2.2.2.2.mul_val_inv

instance integralModel_isElliptic (N : ℕ) : (integralModel N).IsElliptic :=
  ⟨discriminant_unit _ _ (base_units N).1 (base_units N).2.1
    (base_units N).2.2.2.1 (denominator_inverse N)⟩

theorem integralModel_j (N : ℕ) : (integralModel N).j=jCoord N := by
  let : (curve (jCoord N) (inverseDenominator N)).IsElliptic := integralModel_isElliptic N
  exact j_invariant _ _ (denominator_inverse N)

theorem integralModel_discriminant (N : ℕ) :
    (integralModel N).Δ=1728^2*(jCoord N)^2*(inverseDenominator N)^3 :=
  discriminant _ _ (denominator_inverse N)

/-- The same literal elliptic model and j-coordinate survive every ring base change. -/
theorem base_change_elliptic (N : ℕ) (φ : Base N →+* R) :
    ((integralModel N).map φ).IsElliptic := inferInstance

theorem base_change_j (N : ℕ) (φ : Base N →+* R) :
    ((integralModel N).map φ).j=φ (jCoord N) := by
  rw [WeierstrassCurve.map_j,integralModel_j]

end OpenJModel318
#print axioms OpenJModel318.discriminant
#print axioms OpenJModel318.c4
#print axioms OpenJModel318.c4_cube
#print axioms OpenJModel318.discriminant_unit
#print axioms OpenJModel318.j_invariant
#print axioms OpenJModel318.base_units
#print axioms OpenJModel318.denominator_inverse
#print axioms OpenJModel318.integralModel_isElliptic
#print axioms OpenJModel318.integralModel_j
#print axioms OpenJModel318.integralModel_discriminant

#print axioms OpenJModel318.base_change_elliptic
#print axioms OpenJModel318.base_change_j
