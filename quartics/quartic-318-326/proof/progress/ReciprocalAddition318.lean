module
public import GenericFormalAddition318
public section
namespace ReciprocalAddition318
variable {K : Type*} [Field K]

theorem x_polynomial (D u y a b : K) (hy : y^2=1-D*u^4) (hb : b^2=1-D*a^4) :
    ((b*u^3-y*a^3)^2-(u^2+a^2)*(u^2-a^2)^2)*(u*b+a*y)^2 =
      a^2*u^2*(u^2-a^2)^2*(1+D*u^2*a^2)^2 := by
  linear_combination
    a^2*(-D*a^6*u^4+a^6*y^2+2*a^5*b*u*y+a^4*b^2*u^2+a^4*u^2-2*a^3*b*u^3*y-
      4*a^2*b^2*u^4+a^2*u^4+b^2*u^6-u^6)*hy +
    u^4*(-D*a^6*u^2+3*D*a^4*u^4-D*a^2*u^6-3*a^4-2*a^3*b*u*y+2*a^2*u^2+
      2*a*b*u^3*y+b^2*u^4)*hb

theorem y_polynomial (D u y a b : K) (hy : y^2=1-D*u^4) (hb : b^2=1-D*a^4) :
    (b*u^3-y*a^3)*((u*b+a*y)^2-u^2*(1+D*u^2*a^2)^2)*(u*b+a*y)-
      y*a*(u^2-a^2)*(u*b+a*y)^3 =
      (y*b*(1-D*u^2*a^2)-2*D*u*a*(u^2+a^2))*(1+D*u^2*a^2)*a*u^3*(u^2-a^2) := by
  linear_combination
    (-a^3*u^2*(-D^2*a^5*u^4-2*D*a^3*u^2-D*a*u^4+a*y^2+2*b*u*y))*hy +
    u^5*(-D^2*a^4*u^5-D*a^4*u-2*D*a^2*u^3+2*a*b*y+b^2*u)*hb

theorem x_coordinates (D u y a b : K) (hy : y^2=1-D*u^4) (hb : b^2=1-D*a^4)
    (hu : u≠0) (ha : a≠0) (hr : u^2-a^2≠0) (hn : u*b+a*y≠0) :
    ((b*u^3-y*a^3)/(a*u*(u^2-a^2)))^2-1/u^2-1/a^2 =
      (1+D*u^2*a^2)^2/(u*b+a*y)^2 := by
  have h := x_polynomial D u y a b hy hb
  have hn2 : b*u+y*a≠0 := by simpa only [mul_comm] using hn
  field_simp [hu,ha,hr,hn,hn2]
  linear_combination h

theorem y_coordinates (D u y a b : K) (hy : y^2=1-D*u^4) (hb : b^2=1-D*a^4)
    (hu : u≠0) (ha : a≠0) (hr : u^2-a^2≠0) (hn : u*b+a*y≠0) :
    ((b*u^3-y*a^3)/(a*u*(u^2-a^2)))*(1/u^2-(1+D*u^2*a^2)^2/(u*b+a*y)^2)-y/u^3 =
      (y*b*(1-D*u^2*a^2)-2*D*u*a*(u^2+a^2))*(1+D*u^2*a^2)/(u*b+a*y)^3 := by
  have h := y_polynomial D u y a b hy hb
  have hn2 : b*u+y*a≠0 := by simpa only [mul_comm] using hn
  field_simp [hu,ha,hr,hn,hn2]
  linear_combination h

/-- The chord slope on the actual Weierstrass coordinates (1/u²,y/u³)
and (1/a²,b/a³). -/
theorem slope_coordinates (u y a b : K) (hu : u≠0) (ha : a≠0) (hr : u^2-a^2≠0) :
    (b/a^3-y/u^3)/(1/a^2-1/u^2)=(b*u^3-y*a^3)/(a*u*(u^2-a^2)) := by
  have hx : 1/a^2-1/u^2≠0 := by
    intro he
    apply hr
    field_simp [hu,ha] at he
    linear_combination he
  field_simp [hu,ha,hr,hx]

end ReciprocalAddition318
#print axioms ReciprocalAddition318.x_coordinates
#print axioms ReciprocalAddition318.y_coordinates
#print axioms ReciprocalAddition318.slope_coordinates
