module
public import ReciprocalDouble318
public import ReciprocalAddition318
public section
namespace ReciprocalGroup318
open ReciprocalDouble318 WeierstrassCurve.Affine
variable {F:Type*} [Field F] [CharZero F]
noncomputable section
local instance : DecidableEq F := Classical.decEq F
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def sumU (D u v a b:F):F := (u*b+a*v)/(1+D*u^2*a^2)
@[expose] def sumV (D u v a b:F):F :=
  (v*b*(1-D*u^2*a^2)-2*D*u*a*(u^2+a^2))/(1+D*u^2*a^2)^2

theorem sum_curve (D u v a b:F) (hc:v^2=1-D*u^4) (hb:b^2=1-D*a^4)
    (hq:1+D*u^2*a^2≠0) : (sumV D u v a b)^2=1-D*(sumU D u v a b)^4 := by
  dsimp [sumV,sumU]
  field_simp [hq]
  linear_combination
    (D^2*a^4*b^2*u^4-D^2*a^4*u^4+D*a^4*v^2+D*a^4+4*D*a^3*b*u*v+
      4*D*a^2*b^2*u^2+b^2)*hc +
    (-D^3*a^4*u^8-4*D^2*a^2*u^6+4*D*a^2*u^2+4*D*a*b*u^3*v+D*b^2*u^4+1)*hb

theorem numerator_ne (D u v a b:F) (hc:v^2=1-D*u^4) (hb:b^2=1-D*a^4)
    (hq:1+D*u^2*a^2≠0) (hr:u^2-a^2≠0) : u*b+a*v≠0 := by
  intro hn
  have hid:(u^2-a^2)*(1+D*u^2*a^2)=0 := by
    linear_combination -u^2*hb+a^2*hc+(u*b-a*v)*hn
  exact (mul_ne_zero hr hq) hid

theorem secant_actual (D u v a b:F) (hu:u≠0) (ha:a≠0) (hv:v≠0) (hb0:b≠0)
    (hc:v^2=1-D*u^4) (hb:b^2=1-D*a^4) (hq:1+D*u^2*a^2≠0) (hr:u^2-a^2≠0) :
    ∃ h:(E D).Nonsingular (1/(sumU D u v a b)^2) (sumV D u v a b/(sumU D u v a b)^3),
      point D u v hv hc+point D a b hb0 hb=Point.some _ _ h := by
  have hn := numerator_ne D u v a b hc hb hq hr
  have hx:(1:F)/u^2≠1/a^2 := by
    intro he; apply hr
    field_simp [hu,ha] at he
    linear_combination -he
  have hs:(E D).slope (1/u^2) (1/a^2) (v/u^3) (b/a^3)=
      (b*u^3-v*a^3)/(a*u*(u^2-a^2)) := by
    rw [slope_of_X_ne hx]
    have hh:=ReciprocalAddition318.slope_coordinates u v a b hu ha hr
    rw [←neg_div_neg_eq (b/a^3-v/u^3) (1/a^2-1/u^2)] at hh
    simpa only [neg_sub] using hh
  have hxx:(E D).addX (1/u^2) (1/a^2)
      ((E D).slope (1/u^2) (1/a^2) (v/u^3) (b/a^3))=1/(sumU D u v a b)^2 := by
    rw [hs,addX]
    simp only [E,zero_mul,sub_zero,add_zero]
    rw [ReciprocalAddition318.x_coordinates D u v a b hc hb hu ha hr hn]
    dsimp [sumU]
    field_simp [hq,hn]
  have hyy:(E D).addY (1/u^2) (1/a^2) (v/u^3)
      ((E D).slope (1/u^2) (1/a^2) (v/u^3) (b/a^3))=
      sumV D u v a b/(sumU D u v a b)^3 := by
    rw [addY,negAddY,negY,hxx,hs]
    simp only [E,zero_mul,sub_zero]
    have he:=ReciprocalAddition318.y_coordinates D u v a b hc hb hu ha hr hn
    dsimp [sumU,sumV]
    field_simp [hq,hn] at *
    linear_combination he
  have h := nonsingular_add (reciprocal_nonsingular D u v hu hv hc)
    (reciprocal_nonsingular D a b ha hb0 hb) (fun h => hx h.1)
  rw [hxx,hyy] at h
  refine ⟨h,?_⟩
  simp only [point,dite_eq_right hu,dite_eq_right ha]
  rw [Point.add_of_X_ne hx]
  simp only [hxx,hyy]

theorem sumU_double (D u v:F) : sumU D u v u v=uDouble D u v := by
  dsimp [sumU,uDouble]; congr 1 <;> ring

theorem sumV_double (D u v:F) (hc:v^2=1-D*u^4) : sumV D u v u v=vDouble D u := by
  dsimp [sumV,vDouble]
  have hnum:v*v*(1-D*u^2*u^2)-2*D*u*u*(u^2+u^2)=1-6*D*u^4+D^2*u^8 := by
    linear_combination (1-D*u^4)*hc
  rw [hnum]
  congr 2
  ring

/-- Actual reciprocal group law on a normalized branch. The normalization
conditions are precisely the constant-one and same-square root conditions;
no analytic or group-law premise is assumed. -/
theorem actual_add (D u v a b:F) (hv:v≠0) (hb0:b≠0)
    (hc:v^2=1-D*u^4) (hb:b^2=1-D*a^4)
    (hzero:u=0→v=1) (hazero:a=0→b=1) (hbranch:u^2=a^2→v=b)
    (hq:1+D*u^2*a^2≠0) (hout:sumV D u v a b≠0) :
    point D u v hv hc+point D a b hb0 hb=
      point D (sumU D u v a b) (sumV D u v a b) hout (sum_curve D u v a b hc hb hq) := by
  by_cases hu:u=0
  · have hv1:=hzero hu
    subst u; subst v
    simp [point,sumU,sumV]
  by_cases ha:a=0
  · have hb1:=hazero ha
    subst a; subst b
    simp [point,sumU,sumV]
  by_cases hr:u^2=a^2
  · have he:=hbranch hr
    subst b
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr with hea|hea
    · subst a
      have hq':1+D*u^4≠0 := by convert hq using 1 <;> ring
      have hout':vDouble D u≠0 := by rwa [sumV_double D u v hc] at hout
      have hd:=point_double D u v hv hc hq' hout'
      simpa only [sumU_double,sumV_double D u v hc] using hd
    · have hea':a= -u := by linear_combination hea
      subst a
      have hs:sumU D u v (-u) v=0 := by simp [sumU]
      rw [show point D (-u) v hb0 hb= -point D u v hv hc from point_negative D u v hv hc]
      rw [add_neg_cancel]
      simp only [hs,point_zero]
  · have hr':u^2-a^2≠0 := sub_ne_zero.mpr hr
    obtain ⟨h,he⟩ := secant_actual D u v a b hu ha hv hb0 hc hb hq hr'
    have hs:sumU D u v a b≠0 := div_ne_zero (numerator_ne D u v a b hc hb hq hr') hq
    simpa only [point,dite_eq_right hs] using he

end
end ReciprocalGroup318
#print axioms ReciprocalGroup318.actual_add
