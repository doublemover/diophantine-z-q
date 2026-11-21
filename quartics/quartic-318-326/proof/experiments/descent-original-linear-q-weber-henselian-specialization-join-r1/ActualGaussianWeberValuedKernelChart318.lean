module
public import ActualGaussianWeberHenselianPointMap318
public section
noncomputable section

namespace ActualGaussianWeberValuedKernelChart318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberHenselianChart318

variable {F : Type*} [Field F] (V : ValuationSubring F)

@[expose] def tCoord : WP F → F
  | Point.zero => 0
  | Point.some x y _ => -x/y

@[expose] def wCoord : WP F → F
  | Point.zero => 0
  | Point.some _ y _ => -1/y

/-- Genuine normalized chart of an actual point over the same place. -/
structure OriginData (P : WP F) where
  t : V
  w : V
  smallT : t ∈ maximalIdeal V
  smallW : w ∈ maximalIdeal V
  chart : identityChart t w
  t_exact : V.subtype t=tCoord P
  w_exact : V.subtype w=wCoord P

theorem y_ne_of_nonintegral {x y : F} (hx : x ∉ V) (h : y^2=x^3-x) : y ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hx (by simpa only [hx0] using V.zero_mem)
  intro h0
  have hX : x*(x^2-1)=0 := by
    rw [h0,zero_pow (by decide : (2:ℕ) ≠ 0)] at h
    linear_combination -h
  have hx2 : x^2=1 := sub_eq_zero.mp ((mul_eq_zero.mp hX).resolve_left hx0)
  exact hx (integral_square V (hx2.symm ▸ V.one_mem))

/-- This is the actual x-pole branch. Its finite inverse-coordinate
proof uses only valuation subring square closure, not a value-group
exponent or Henselianity. -/
theorem from_nonintegral {x y : F} (hx : x ∉ V)
    (hn : (curve F).toAffine.Nonsingular x y) :
    Nonempty (OriginData V (Point.some x y hn)) := by
  have h := (literal_equation x y).mp hn.1
  have hx0 : x ≠ 0 := by
    intro h0
    exact hx (by simpa only [h0] using V.zero_mem)
  have hy0 := y_ne_of_nonintegral V hx h
  let z : V := ⟨x⁻¹,(V.mem_or_inv_mem x).resolve_left hx⟩
  have hzI : z ∈ maximalIdeal V := by
    change ¬IsUnit z
    rintro ⟨u,hu⟩
    have hi : V.subtype (↑u⁻¹:V)*x⁻¹=1 := by
      change V.subtype (↑u⁻¹:V)*V.subtype z=1
      rw [←hu,←map_mul,u.inv_mul,map_one]
    have he : V.subtype (↑u⁻¹:V)=x := by
      calc
        _ = V.subtype (↑u⁻¹:V)*1 := (mul_one _).symm
        _ = _ := by rw [←inv_mul_cancel₀ hx0,←mul_assoc,hi,one_mul]
    exact hx (he ▸ (↑u⁻¹:V).property)
  have hz0 := (residue_eq_zero_iff z).mpr hzI
  have hU : IsUnit (1-z^2) := (residue_ne_zero_iff_isUnit _).mp (by
    simp only [map_sub,map_one,map_pow,hz0,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero]
    exact one_ne_zero)
  obtain ⟨u,hu⟩ := hU
  let s : V := z*(↑u⁻¹:V)
  have hsI : s ∈ maximalIdeal V := (maximalIdeal V).mul_mem_right _ hzI
  have hsu : s*(u:V)=z := by
    change z*(↑u⁻¹:V)*(u:V)=z
    rw [mul_assoc,u.inv_mul,mul_one]
  have hsD : V.subtype s * V.subtype (u:V)=x⁻¹ := by
    rw [←map_mul,hsu] <;> rfl
  have huD : V.subtype (u:V)=1-(x⁻¹)^2 := by
    rw [hu,map_sub,map_one,map_pow] <;> rfl
  have hUF : V.subtype (u:V) ≠ 0 := by
    intro H
    exact (Units.ne_zero u) (V.subtype_injective (H.trans (map_zero _).symm))
  have htD : (-x/y)^2 * (1-(x⁻¹)^2)=x⁻¹ := by
    calc
      _ = (x^2-1)/y^2 := by field_simp [hx0,hy0] <;> ring
      _ = x⁻¹ := by
        apply (div_eq_iff (pow_ne_zero 2 hy0)).mpr
        have hY : y^2=x*(x^2-1) := by linear_combination h
        rw [hY,←mul_assoc,inv_mul_cancel₀ hx0,one_mul]
  have ht2 : (-x/y)^2 = V.subtype s := by
    apply mul_right_cancel₀ hUF
    rw [hsD,huD,htD]
  have htV : -x/y ∈ V := integral_square V (ht2.symm ▸ s.property)
  let t : V := ⟨-x/y,htV⟩
  have ht2' : t^2=s := V.subtype_injective (by rw [map_pow]; exact ht2)
  have htI : t ∈ maximalIdeal V := by
    apply (residue_eq_zero_iff t).mp
    have hh : (residue V t)^2=0 := by
      rw [←map_pow,ht2',(residue_eq_zero_iff s).mpr hsI]
    by_contra H
    exact (pow_ne_zero 2 H) hh
  let w : V := t*z
  have hw : V.subtype w = -1/y := by
    change V.subtype (t*z) = _
    rw [map_mul]
    change (-x/y)*x⁻¹ = _
    field_simp [hx0,hy0] <;> ring
  have hc : identityChart t w := by
    unfold identityChart
    apply V.subtype_injective
    rw [map_add,map_mul,map_pow,map_pow,hw]
    change -1/y + (-x/y)*(-1/y)^2=(-x/y)^3
    apply mul_right_cancel₀ (pow_ne_zero 3 hy0)
    have hl : (-1/y+(-x/y)*(-1/y)^2)*y^3= -(y^2+x) := by
      field_simp [hy0] <;> ring
    have hr : ((-x/y)^3)*y^3= -(x^3) := by
      field_simp [hy0] <;> ring
    rw [hl,hr]
    linear_combination -h
  exact ⟨⟨t,w,htI,(maximalIdeal V).mul_mem_right z htI,hc,rfl,hw⟩⟩

theorem from_kernel (h2 : (2:ResidueField V) ≠ 0) (P : WP F)
    (hP : specialize V h2 P = Point.zero) : Nonempty (OriginData V P) := by
  cases P with
  | zero =>
    refine ⟨⟨0,0,(maximalIdeal V).zero_mem,(maximalIdeal V).zero_mem,?_,?_,?_⟩⟩
    · simp [identityChart]
    · simp [tCoord]
    · simp [wCoord]
  | some x y h => exact from_nonintegral V ((specialize_some_eq_zero V h2 h).mp hP) h

theorem point_zero_of_chart_zero (h2 : (2:ResidueField V) ≠ 0) {P : WP F}
    (hP : specialize V h2 P = Point.zero) (d : OriginData V P) (ht : d.t=0) :
    P=Point.zero := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hx := (specialize_some_eq_zero V h2 h).mp hP
    have hy := y_ne_of_nonintegral V hx ((literal_equation x y).mp h.1)
    have ht' : -x/y=0 := by simpa only [ht,map_zero,tCoord] using d.t_exact.symm
    have hx0 : x=0 := by
      have h0 := (div_eq_iff hy).mp ht'
      simpa only [zero_mul,neg_eq_zero] using h0
    exact False.elim (hx (hx0 ▸ V.zero_mem))

end ActualGaussianWeberValuedKernelChart318
