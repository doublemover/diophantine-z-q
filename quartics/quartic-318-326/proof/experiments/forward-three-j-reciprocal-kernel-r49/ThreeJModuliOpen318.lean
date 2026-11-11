module
public import ThreeJGlobalFinite318
public import ModularArithmeticCoordinates318
public section
noncomputable section
namespace ThreeJModuliOpen318
open Polynomial AlgebraicGeometry CategoryTheory
open ThreeJLaurentEquiv318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual Laurent source localized at the pullback of j(j-1728).
This is a rational open, not a claimed extension of the integral model at3. -/
@[expose] def deleted : Laurent := jLaurent*(jLaurent-1728)
abbrev Ring := Localization.Away deleted
@[expose] def inclusion : Laurent →ₐ[ℚ] Ring := IsScalarTower.toAlgHom ℚ Laurent Ring
@[expose] def t : Ring := inclusion ProjectiveLineOverlap318.t
@[expose] def s : Ring := inclusion ProjectiveLineOverlap318.s
@[expose] def j : Ring := inclusion jLaurent
@[expose] def d : Ring := t^2-486*t-19683
@[expose] def n : Ring := (t+27)*(t+243)^3

lemma ts : t*s=1 := by
  simpa only [t,s,map_mul,map_one] using congrArg inclusion ProjectiveLineOverlap318.ts
lemma j_eq : j=n*s^3 := by
  simp only [j,jLaurent,n,t,s,map_mul,map_pow,map_add,map_ofNat]
lemma j_sub : j-1728=d^2*s^3 := by
  have h : t^3*s^3=1 := by rw [←mul_pow,ts,one_pow]
  rw [j_eq]
  unfold n d
  linear_combination 1728*h
lemma j_units : IsUnit j ∧ IsUnit (j-1728) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S:=Ring) deleted
  simpa only [deleted,map_mul,map_sub,map_ofNat,IsUnit.mul_iff,j,inclusion,
    IsScalarTower.toAlgHom_apply] using h
lemma d_unit : IsUnit d := by
  have h := j_units.2
  rw [j_sub] at h
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (IsUnit.mul_iff.mp h).1
@[expose] def v : Ring := ↑d_unit.unit⁻¹
lemma dv : d*v=1 := d_unit.mul_val_inv
@[expose] def k : Ring := n*v^2
@[expose] def x : Ring := 3*(t+27)*(t+243)*v

lemma k_j_sub : k*(j-1728)=j := by
  have hv : d^2*v^2=1 := by rw [←mul_pow,dv,one_pow]
  rw [j_sub,j_eq]
  unfold k
  linear_combination n*s^3*hv

/-- The normalized original third-division equation, proved inside the
actual localized source ring rather than only after complex evaluation. -/
lemma root_relation : x^4-6*k*x^2-8*k*x-3*k^2=0 := by
  have h := dv
  unfold x k n d at *
  linear_combination 24*(t+27)^2*(t+243)^4*v^3*h

@[expose] def basePolynomial : Polynomial ℤ →+* Ring :=
  Polynomial.eval₂RingHom (Int.castRingHom Ring) j
lemma base_denominator_unit : IsUnit (basePolynomial (OpenJModel318.denominator 3)) := by
  have h18 : IsUnit (18:Ring) := by
    have h : IsUnit (18:ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using h.map (algebraMap ℚ Ring)
  have he : basePolynomial X=j := Polynomial.eval₂_X _ _
  simpa only [OpenJModel318.denominator,map_mul,map_sub,map_natCast,map_ofNat,he,
    show (6:Ring)*((3:ℕ):Ring)=18 by norm_num] using (h18.mul j_units.1).mul j_units.2


/-- Actual base map from Z[1/18,j,1/(j(j-1728))] to the rational source open. -/
@[expose] def baseMap : OpenJModel318.Base 3 →+* Ring :=
  IsLocalization.Away.lift (OpenJModel318.denominator 3) base_denominator_unit
lemma base_j : baseMap (OpenJModel318.jCoord 3)=j := by
  simp [baseMap,OpenJModel318.jCoord,basePolynomial]
lemma base_inverse : baseMap (OpenJModel318.inverseDenominator 3)*(j-1728)=1 := by
  have h := congrArg baseMap (OpenJModel318.denominator_inverse 3)
  simpa only [map_mul,map_sub,map_ofNat,map_one,base_j,mul_comm] using h
lemma base_ratio : j*baseMap (OpenJModel318.inverseDenominator 3)=k := by
  calc
    _ = (k*(j-1728))*baseMap (OpenJModel318.inverseDenominator 3) := by rw [k_j_sub]
    _ = k := by rw [mul_assoc,mul_comm (j-1728),base_inverse,mul_one]
lemma base_A : baseMap (OpenJAffineScheme318.A 3)= -3*k := by
  simp only [OpenJAffineScheme318.A,map_mul,map_neg,map_ofNat,base_j]
  rw [mul_assoc,base_ratio]
lemma base_B : baseMap (OpenJAffineScheme318.B 3)= -2*k := by
  simp only [OpenJAffineScheme318.B,map_mul,map_neg,map_ofNat,base_j]
  rw [mul_assoc,base_ratio]

/-- Literal original elliptic family after the constructed base change. -/
@[expose] def family : WeierstrassCurve Ring := (OpenJModel318.integralModel 3).map baseMap
instance family_isElliptic : family.IsElliptic := OpenJModel318.base_change_elliptic 3 baseMap
lemma family_j : family.j=j := by
  exact (OpenJModel318.base_change_j 3 baseMap).trans base_j

end ThreeJModuliOpen318
