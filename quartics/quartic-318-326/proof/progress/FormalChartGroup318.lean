module
public import FormalChordAlgebra318
public import ReciprocalDouble318
public section
namespace FormalChartGroup318
open FormalChordAlgebra318 ReciprocalDouble318 WeierstrassCurve.Affine
variable {F:Type*} [Field F] [CharZero F] [DecidableEq F]
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma nu_ne_of_X_ne (D z₁ t₁ z₂ t₂:F)
    (h₁:t₁=z₁^3-D*z₁*t₁^2) (h₂:t₂=z₂^3-D*z₂*t₂^2)
    (ht₁:t₁≠0) (ht₂:t₂≠0) (hd:1+D*z₁*(t₁+t₂)≠0)
    (hx:z₁/t₁≠z₂/t₂) : nu D z₁ t₁ z₂ t₂≠0 := by
  intro hv
  have hl₁:=line_one D z₁ t₁ z₂ t₂
  have hl₂:=line_two D z₁ t₁ z₂ t₂ h₁ h₂ hd
  rw [hv,add_zero] at hl₁ hl₂
  apply hx
  apply (div_eq_div_iff ht₁ ht₂).mpr
  linear_combination z₁*hl₂-z₂*hl₁

/-- The actual affine secant addition, expressed in the standard formal
chart. This algebraic identity applies over every characteristic-zero field. -/
theorem actual_secant (D z₁ t₁ z₂ t₂:F)
    (h₁:t₁=z₁^3-D*z₁*t₁^2) (h₂:t₂=z₂^3-D*z₂*t₂^2)
    (ht₁:t₁≠0) (ht₂:t₂≠0) (hd:1+D*z₁*(t₁+t₂)≠0)
    (hz:z₁≠z₂) (hx:z₁/t₁≠z₂/t₂)
    (hn₁:(E D).Nonsingular (z₁/t₁) (-1/t₁))
    (hn₂:(E D).Nonsingular (z₂/t₂) (-1/t₂))
    (hq:1-D*(lambda D z₁ t₁ z₂ t₂)^2≠0) :
    let l:=lambda D z₁ t₁ z₂ t₂
    let v:=nu D z₁ t₁ z₂ t₂
    let z₃:=thirdZ D l v z₁ z₂
    let t₃:=l*z₃+v
    t₃≠0 ∧ z₃≠0 ∧
    ∃hn₃:(E D).Nonsingular (z₃/t₃) (1/t₃),
      Point.some _ _ hn₁+Point.some _ _ hn₂=Point.some _ _ hn₃ := by
  dsimp only
  let l:=lambda D z₁ t₁ z₂ t₂
  let v:=nu D z₁ t₁ z₂ t₂
  let z₃:=thirdZ D l v z₁ z₂
  let t₃:=l*z₃+v
  have hl₁:t₁=l*z₁+v:=line_one D z₁ t₁ z₂ t₂
  have hl₂:t₂=l*z₂+v:=line_two D z₁ t₁ z₂ t₂ h₁ h₂ hd
  have hv:v≠0:=nu_ne_of_X_ne D z₁ t₁ z₂ t₂ h₁ h₂ ht₁ ht₂ hd hx
  have hc₁:l*z₁+v=z₁^3-D*z₁*(l*z₁+v)^2 := by rw [←hl₁]; exact h₁
  have hc₂:l*z₂+v=z₂^3-D*z₂*(l*z₂+v)^2 := by rw [←hl₂]; exact h₂
  obtain ⟨hs,hp,hm⟩:=vieta D l v z₁ z₂ hz hq hc₁ hc₂
  have htprod:=product_line_values D l v z₁ z₂ z₃ hq hs hp hm
  have ht₃:t₃≠0 := by
    intro he
    change (l*z₁+v)*(l*z₂+v)*t₃=_ at htprod
    rw [he,mul_zero] at htprod
    exact (div_ne_zero (pow_ne_zero _ hv) hq) htprod.symm
  have hz₃:z₃≠0 := by
    intro he
    change z₁*z₂*z₃=_ at hm
    rw [he,mul_zero] at hm
    exact (div_ne_zero hv hq) hm.symm
  have hsum:=sum_abscissas D l v z₁ z₂ z₃ hq hv hs hp hm
  rw [←hl₁,←hl₂] at hsum
  have hslope:(E D).slope (z₁/t₁) (z₂/t₂) (-1/t₁) (-1/t₂)=l/v := by
    rw [slope_of_X_ne hx]
    apply (div_eq_div_iff (sub_ne_zero.mpr hx) hv).mpr
    field_simp [ht₁,ht₂]
    linear_combination t₂*hl₁-t₁*hl₂
  have hxsum:(E D).addX (z₁/t₁) (z₂/t₂)
      ((E D).slope (z₁/t₁) (z₂/t₂) (-1/t₁) (-1/t₂))=z₃/t₃ := by
    rw [hslope,addX]
    simp only [E,zero_mul,add_zero,sub_zero]
    change (l/v)^2-z₁/t₁-z₂/t₂=z₃/t₃
    linear_combination -hsum
  have hysum:(E D).addY (z₁/t₁) (z₂/t₂) (-1/t₁)
      ((E D).slope (z₁/t₁) (z₂/t₂) (-1/t₁) (-1/t₂))=1/t₃ := by
    rw [addY,negAddY,hxsum,hslope,negY]
    simp only [E,zero_mul,sub_zero]
    change -(l/v*(z₃/t₃-z₁/t₁)+(-1/t₁))=1/t₃
    have htdef:t₃=l*z₃+v:=rfl
    field_simp [hv,ht₁,ht₃]
    linear_combination -t₃*hl₁+t₁*htdef
  have hn₃:=nonsingular_add hn₁ hn₂ (fun h=>hx h.1)
  rw [hxsum,hysum] at hn₃
  refine ⟨ht₃,hz₃,hn₃,?_⟩
  rw [Point.add_of_X_ne hx]
  simp only [hxsum,hysum]
  rfl

#print axioms actual_secant
end
end FormalChartGroup318
