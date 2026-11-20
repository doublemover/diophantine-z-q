module
public import SelectedPeriodCubicNonsingular318
public import NormalizedWeierstrass318
public import WeierstrassChord318
public import WeierstrassAvoidance318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace SelectedPeriodPointGroup318

open ChordAlgebra318 ChordFlow318
attribute [local instance] Classical.propDecidable
variable (P : PeriodPair)

@[expose] def curve : WeierstrassCurve ℂ :=
  NormalizedWeierstrass318.model (12*P.g₂) (216*P.g₃)

theorem discriminant : (curve P).Δ = P.g₂^3-27*P.g₃^2 := by
  rw [curve,NormalizedWeierstrass318.model_discriminant]
  ring

instance curve_isElliptic : (curve P).IsElliptic :=
  ⟨by rw [discriminant]; exact isUnit_iff_ne_zero.mpr
    (SelectedPeriodCubicNonsingular318.discriminant_ne_zero P)⟩

theorem equation_iff (x y : ℂ) : (curve P).toAffine.Equation x y ↔
    (2*y)^2 = 4*x^3-P.g₂*x-P.g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y^2+0*x*y+0*y=x^3+0*x^2+(-(12*P.g₂)/48)*x+(-(216*P.g₃)/864) ↔ _
  constructor
  · intro h; linear_combination 4*h
  · intro h; linear_combination h/4

theorem nonsingular (z : ℂ) (hz : z ∉ P.lattice) :
    (curve P).toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z/2) := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (show (curve P).Δ ≠ 0 by
      rw [discriminant]
      exact SelectedPeriodCubicNonsingular318.discriminant_ne_zero P)).mp
  rw [equation_iff]
  convert P.derivWeierstrassP_sq z hz using 1 <;> ring

/-- The independently defined native algebraic group, evaluated
on the actual period functions rather than transported from a quotient. -/
@[expose] def rawPoint (z : ℂ) : (curve P).toAffine.Point :=
  if hz : z ∈ P.lattice then 0 else
    .some (P.weierstrassP z) (P.derivWeierstrassP z/2) (nonsingular P z hz)

theorem rawPoint_mem (z : ℂ) (hz : z ∈ P.lattice) : rawPoint P z = 0 :=
  dif_pos hz

theorem rawPoint_nonperiod (z : ℂ) (hz : z ∉ P.lattice) :
    rawPoint P z =
      .some (P.weierstrassP z) (P.derivWeierstrassP z/2) (nonsingular P z hz) :=
  dif_neg hz

theorem rawPoint_eq_zero (z : ℂ) : rawPoint P z = 0 ↔ z ∈ P.lattice := by
  by_cases hz : z ∈ P.lattice
  · simp [rawPoint_mem P z hz,hz]
  · rw [rawPoint_nonperiod P z hz]
    simp only [WeierstrassCurve.Affine.Point.some_ne_zero,hz]

theorem rawPoint_period (z : ℂ) (a : P.lattice) : rawPoint P (z+a.val) = rawPoint P z := by
  have hm : z+a.val ∈ P.lattice ↔ z ∈ P.lattice :=
    P.lattice.toAddSubgroup.add_mem_cancel_right a.property
  by_cases hz : z ∈ P.lattice
  · rw [rawPoint_mem P z hz,rawPoint_mem P _ (hm.mpr hz)]
  · rw [rawPoint_nonperiod P z hz,rawPoint_nonperiod P _ (fun h => hz (hm.mp h)),
      WeierstrassCurve.Affine.Point.some.injEq,P.weierstrassP_add_coe,
      P.derivWeierstrassP_add_coe] <;> exact ⟨rfl,rfl⟩

theorem rawPoint_neg (z : ℂ) : rawPoint P (-z) = -rawPoint P z := by
  by_cases hz : z ∈ P.lattice
  · rw [rawPoint_mem P z hz,rawPoint_mem P (-z) (P.lattice.neg_mem hz),neg_zero]
  have hn : -z ∉ P.lattice := fun h => hz (by simpa using P.lattice.neg_mem h)
  rw [rawPoint_nonperiod P _ hn,rawPoint_nonperiod P _ hz,
    WeierstrassCurve.Affine.Point.neg_def]
  simp [WeierstrassCurve.Affine.Point.neg,P.weierstrassP_neg,P.derivWeierstrassP_neg,
    WeierstrassCurve.Affine.negY,curve,NormalizedWeierstrass318.model,neg_div]

theorem rawPoint_add_chord (z w : ℂ) (hz : z ∉ P.lattice) (hw : w ∉ P.lattice)
    (hx : P.weierstrassP z-P.weierstrassP w ≠ 0)
    (hb : P.derivWeierstrassP w ≠ 0) :
    rawPoint P (z+w) = rawPoint P z+rawPoint P w := by
  have hxn : P.weierstrassP w ≠ P.weierstrassP z := (sub_ne_zero.mp hx).symm
  obtain ⟨hR,hY⟩ := WeierstrassChord318.chord_pair P z w hz hw hx hb
  have hs := WeierstrassChord318.sum_not_mem P z w hx
  rw [rawPoint_nonperiod P _ hs,rawPoint_nonperiod P z hz,rawPoint_nonperiod P w hw]
  conv_rhs => rw [add_comm]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxn,
    WeierstrassCurve.Affine.Point.some.injEq,WeierstrassCurve.Affine.slope_of_X_ne hxn]
  have hsl : (P.derivWeierstrassP w/2-P.derivWeierstrassP z/2)/
      (P.weierstrassP w-P.weierstrassP z) =
      ChordAlgebra318.slope (P.weierstrassP w) (P.derivWeierstrassP w)
        (P.weierstrassP z) (P.derivWeierstrassP z)/2 := by
    unfold ChordAlgebra318.slope
    field_simp [hx,sub_ne_zero.mpr hxn] <;> ring
  rw [hsl]
  simp only [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.negAddY,
    curve,NormalizedWeierstrass318.model,zero_mul,sub_zero]
  rw [←hR,←hY]
  simp only [R,Y,chordY,chordX]
  constructor <;> field_simp <;> ring

/-- This is the actual additive uniformization: tangent and exceptional
cases reduce to the same ordinary chord by an auxiliary translate. -/
theorem rawPoint_add (z w : ℂ) : rawPoint P (z+w) = rawPoint P z+rawPoint P w := by
  by_cases hz : z ∈ P.lattice
  · rw [rawPoint_mem P z hz,zero_add]
    simpa only [add_comm] using rawPoint_period P w ⟨z,hz⟩
  by_cases hw : w ∈ P.lattice
  · rw [rawPoint_mem P w hw,add_zero]
    exact rawPoint_period P z ⟨w,hw⟩
  by_cases hs : z+w ∈ P.lattice
  · have hp := rawPoint_period P (-z) ⟨z+w,hs⟩
    have hn : rawPoint P w = -rawPoint P z := by
      simpa only [neg_add_cancel_left,rawPoint_neg] using hp
    rw [rawPoint_mem P (z+w) hs,hn,add_neg_cancel]
  obtain ⟨v,hv,hzv,hdv,hdzv,hxvz,hxvzw,hxzvw⟩ :=
    WeierstrassAvoidance318.exists_auxiliary P z w
  have h1 := rawPoint_add_chord P z v hz hv (sub_ne_zero.mpr hxvz.symm) hdv
  have h2 := rawPoint_add_chord P w (z+v) hw hzv (sub_ne_zero.mpr hxzvw.symm) hdzv
  have h3 := rawPoint_add_chord P (z+w) v hs hv (sub_ne_zero.mpr hxvzw.symm) hdv
  have hc : rawPoint P (z+w)+rawPoint P v = (rawPoint P z+rawPoint P w)+rawPoint P v := by
    calc
      rawPoint P (z+w)+rawPoint P v = rawPoint P ((z+w)+v) := h3.symm
      _ = rawPoint P (w+(z+v)) := by congr 1; ring
      _ = rawPoint P w+rawPoint P (z+v) := h2
      _ = (rawPoint P z+rawPoint P w)+rawPoint P v := by rw [h1]; abel
  exact add_right_cancel hc

@[expose] def rawHom : ℂ →+ (curve P).toAffine.Point where
  toFun := rawPoint P
  map_zero' := rawPoint_mem P 0 P.lattice.zero_mem
  map_add' := rawPoint_add P

theorem rawHom_surjective : Function.Surjective (rawHom P) := by
  intro a
  cases a with
  | zero => exact ⟨0,map_zero (rawHom P)⟩
  | some x y hn =>
    have he := ((WeierstrassCurve.Affine.nonsingular_iff x y).mp hn).1
    obtain ⟨z,hz,hx,hy⟩ := SelectedPeriodCubicSurjectivity318.exists_cubic_point P
      x (2*y) ((equation_iff P x y).mp he)
    refine ⟨z,?_⟩
    change rawPoint P z = _
    rw [rawPoint_nonperiod P z hz,WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,by rw [hy]; ring⟩

theorem ker_rawHom : (rawHom P).ker = P.lattice.toAddSubgroup := by
  ext z
  exact rawPoint_eq_zero P z

@[expose] def pointHom :
    ℂ ⧸ P.lattice.toAddSubgroup →+ (curve P).toAffine.Point :=
  QuotientAddGroup.lift P.lattice.toAddSubgroup (rawHom P)
    (by rw [ker_rawHom P])

theorem pointHom_mk (z : ℂ) :
    pointHom P (QuotientAddGroup.mk' P.lattice.toAddSubgroup z) = rawPoint P z := rfl

theorem pointHom_bijective : Function.Bijective (pointHom P) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have hq : pointHom P (a-b) = 0 := by rw [map_sub,hab,sub_self]
    obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective P.lattice.toAddSubgroup (a-b)
    rw [←hz,pointHom_mk] at hq
    rw [←hz]
    exact (QuotientAddGroup.eq_zero_iff z).mpr ((rawPoint_eq_zero P z).mp hq)
  · intro a
    obtain ⟨z,hz⟩ := rawHom_surjective P a
    exact ⟨QuotientAddGroup.mk' P.lattice.toAddSubgroup z,hz⟩

@[expose] def additiveUniformization :
    (ℂ ⧸ P.lattice.toAddSubgroup) ≃+ (curve P).toAffine.Point :=
  AddEquiv.ofBijective (pointHom P) (pointHom_bijective P)

end SelectedPeriodPointGroup318

#print axioms SelectedPeriodPointGroup318.rawPoint_add
#print axioms SelectedPeriodPointGroup318.pointHom_mk
#print axioms SelectedPeriodPointGroup318.pointHom_bijective
#print axioms SelectedPeriodPointGroup318.additiveUniformization
