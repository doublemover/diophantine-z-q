module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic
public section
namespace FormalChordAlgebra318
variable {F:Type*} [Field F] [CharZero F]
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def lambda (D z₁ t₁ z₂ t₂:F) : F :=
  (z₁^2+z₁*z₂+z₂^2-D*t₂^2)/(1+D*z₁*(t₁+t₂))
@[expose] def nu (D z₁ t₁ z₂ t₂:F) : F := t₁-lambda D z₁ t₁ z₂ t₂*z₁
@[expose] def thirdZ (D l v z₁ z₂:F) : F := 2*D*l*v/(1-D*l^2)-z₁-z₂

lemma difference (D z₁ t₁ z₂ t₂:F)
    (h₁:t₁=z₁^3-D*z₁*t₁^2) (h₂:t₂=z₂^3-D*z₂*t₂^2)
    (hd:1+D*z₁*(t₁+t₂)≠0) :
    t₁-t₂=lambda D z₁ t₁ z₂ t₂*(z₁-z₂) := by
  dsimp [lambda]
  rw [div_mul_eq_mul_div,eq_div_iff hd]
  linear_combination h₁-h₂

lemma line_one (D z₁ t₁ z₂ t₂:F) :
    t₁=lambda D z₁ t₁ z₂ t₂*z₁+nu D z₁ t₁ z₂ t₂ := by dsimp [nu]; ring
lemma line_two (D z₁ t₁ z₂ t₂:F)
    (h₁:t₁=z₁^3-D*z₁*t₁^2) (h₂:t₂=z₂^3-D*z₂*t₂^2)
    (hd:1+D*z₁*(t₁+t₂)≠0) :
    t₂=lambda D z₁ t₁ z₂ t₂*z₂+nu D z₁ t₁ z₂ t₂ := by
  have hh:=difference D z₁ t₁ z₂ t₂ h₁ h₂ hd
  dsimp [nu]
  linear_combination -hh

lemma cubic_root (D l v z:F) (h:l*z+v=z^3-D*z*(l*z+v)^2) :
    (1-D*l^2)*z^3-2*D*l*v*z^2-(D*v^2+l)*z-v=0 := by
  linear_combination -h

lemma vieta (D l v z₁ z₂:F) (hz:z₁≠z₂) (hq:1-D*l^2≠0)
    (h₁:l*z₁+v=z₁^3-D*z₁*(l*z₁+v)^2)
    (h₂:l*z₂+v=z₂^3-D*z₂*(l*z₂+v)^2) :
    let z₃:=thirdZ D l v z₁ z₂
    z₁+z₂+z₃=2*D*l*v/(1-D*l^2) ∧
    z₁*z₂+z₁*z₃+z₂*z₃= -(D*v^2+l)/(1-D*l^2) ∧
    z₁*z₂*z₃=v/(1-D*l^2) := by
  have hr₁:=cubic_root D l v z₁ h₁
  have hr₂:=cubic_root D l v z₂ h₂
  have hp:(1-D*l^2)*(z₁^2+z₁*z₂+z₂^2)-2*D*l*v*(z₁+z₂)-(D*v^2+l)=0 := by
    apply (mul_eq_zero.mp (show (z₁-z₂)*((1-D*l^2)*(z₁^2+z₁*z₂+z₂^2)-
      2*D*l*v*(z₁+z₂)-(D*v^2+l))=0 by linear_combination hr₁-hr₂)).resolve_left
      (sub_ne_zero.mpr hz)
  dsimp [thirdZ]
  refine ⟨by ring,?_,?_⟩
  · field_simp [hq]
    linear_combination -hp
  · field_simp [hq]
    linear_combination hr₁-z₁*hp

lemma third_curve (D l v z₁ z₂:F) (hz:z₁≠z₂) (hq:1-D*l^2≠0)
    (h₁:l*z₁+v=z₁^3-D*z₁*(l*z₁+v)^2)
    (h₂:l*z₂+v=z₂^3-D*z₂*(l*z₂+v)^2) :
    l*thirdZ D l v z₁ z₂+v=(thirdZ D l v z₁ z₂)^3-
      D*thirdZ D l v z₁ z₂*(l*thirdZ D l v z₁ z₂+v)^2 := by
  obtain ⟨hs,hp,hm⟩:=vieta D l v z₁ z₂ hz hq h₁ h₂
  let z₃:=thirdZ D l v z₁ z₂
  have hs':(1-D*l^2)*(z₁+z₂+z₃)=2*D*l*v := by
    dsimp [z₃]; rw [hs]; field_simp
  have hp':(1-D*l^2)*(z₁*z₂+z₁*z₃+z₂*z₃)= -(D*v^2+l) := by
    dsimp [z₃]; rw [hp]; field_simp
  have hm':(1-D*l^2)*(z₁*z₂*z₃)=v := by
    dsimp [z₃]; rw [hm]; field_simp
  change l*z₃+v=z₃^3-D*z₃*(l*z₃+v)^2
  linear_combination -z₃^2*hs'+z₃*hp'-hm'

lemma product_line_values (D l v z₁ z₂ z₃:F) (hq:1-D*l^2≠0)
    (hs:z₁+z₂+z₃=2*D*l*v/(1-D*l^2))
    (hp:z₁*z₂+z₁*z₃+z₂*z₃= -(D*v^2+l)/(1-D*l^2))
    (hm:z₁*z₂*z₃=v/(1-D*l^2)) :
    (l*z₁+v)*(l*z₂+v)*(l*z₃+v)=v^3/(1-D*l^2) := by
  calc
    _ = l^3*(z₁*z₂*z₃)+l^2*v*(z₁*z₂+z₁*z₃+z₂*z₃)+l*v^2*(z₁+z₂+z₃)+v^3 := by ring
    _ = _ := by
      rw [hs,hp,hm]
      generalize hdef : 1-D*l^2=q at *
      field_simp [hq]
      linear_combination -v^3*hdef

lemma sum_abscissas (D l v z₁ z₂ z₃:F) (hq:1-D*l^2≠0) (hv:v≠0)
    (hs:z₁+z₂+z₃=2*D*l*v/(1-D*l^2))
    (hp:z₁*z₂+z₁*z₃+z₂*z₃= -(D*v^2+l)/(1-D*l^2))
    (hm:z₁*z₂*z₃=v/(1-D*l^2)) :
    z₁/(l*z₁+v)+z₂/(l*z₂+v)+z₃/(l*z₃+v)=(l/v)^2 := by
  have ht:=product_line_values D l v z₁ z₂ z₃ hq hs hp hm
  have htne:(l*z₁+v)*(l*z₂+v)*(l*z₃+v)≠0 := by rw [ht]; exact div_ne_zero (pow_ne_zero _ hv) hq
  have h1:l*z₁+v≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htne).1).1
  have h2:l*z₂+v≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htne).1).2
  have h3:l*z₃+v≠0 := (mul_ne_zero_iff.mp htne).2
  have hn:z₁*(l*z₂+v)*(l*z₃+v)+z₂*(l*z₁+v)*(l*z₃+v)+z₃*(l*z₁+v)*(l*z₂+v)=l^2*v/(1-D*l^2) := by
    calc
      _ = 3*l^2*(z₁*z₂*z₃)+2*l*v*(z₁*z₂+z₁*z₃+z₂*z₃)+v^2*(z₁+z₂+z₃) := by ring
      _ = _ := by rw [hs,hp,hm]; field_simp [hq]; ring
  have he:v^2*(z₁*(l*z₂+v)*(l*z₃+v)+z₂*(l*z₁+v)*(l*z₃+v)+z₃*(l*z₁+v)*(l*z₂+v))=
      l^2*((l*z₁+v)*(l*z₂+v)*(l*z₃+v)) := by rw [hn,ht]; ring
  generalize h1def : l*z₁+v=t₁ at *
  generalize h2def : l*z₂+v=t₂ at *
  generalize h3def : l*z₃+v=t₃ at *
  field_simp [h1,h2,h3,hv]
  linear_combination he

#print axioms vieta
#print axioms third_curve
#print axioms sum_abscissas
end
end FormalChordAlgebra318
