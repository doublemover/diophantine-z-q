module
public import ActualLogIdentification318
public import JLinear318
public section
namespace ActualJLog318
open ActualLogHom318 ReciprocalDouble318 WeierstrassCurve.Affine
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- On the positive reciprocal branch, the actual point logarithm is the
full H integral, including the identity branch. -/
theorem logarithm_reciprocal (hp : 19≤p) (D u v : ℚ_[p]) (hv : v≠0)
    (hc : v^2=1-D*u^4) (hw : ‖D*u^4‖<1) (hnear : ‖v-1‖<1) :
    logarithm p hp D (point D u v hv hc)= -u*HTail318.H p (D*u^4) := by
  by_cases hu : u=0
  · subst u
    simp [point,logarithm,recover]
  · have hroot : CanonicalRoot318.root p hp (D*u^4)=v :=
      CanonicalRoot318.root_unique p hp _ _ _ (CanonicalRoot318.root_spec p hp _ hw).1 hc
        (CanonicalRoot318.root_spec p hp _ hw).2 hnear
    have harg : D/(1/u^2)^2=D*u^4 := by field_simp
    have hrec : (1/u^2)*v/(v/u^3)=u := by field_simp [hu,hv]
    simp only [point,dite_eq_right hu,logarithm,recover,harg,hroot,hrec]

/-- Actual J identification used by the alternate source charts. -/
theorem logarithm_J (hp : 19≤p) (D u v : ℚ_[p]) (hv : v≠0)
    (hc : v^2=1-D*u^4) (hw : ‖D*u^4‖<1) (hnear : ‖v-1‖<1) :
    logarithm p hp D (point D u v hv hc)= -u*JTail318.J p (v-1) := by
  rw [logarithm_reciprocal p hp D u v hv hc hw hnear,JTail318.J]
  have he : D*u^4= -2*(v-1)-(v-1)^2 := by linear_combination hc
  rw [he]

theorem actual_J_pade_error (hp : 19≤p) (D u v : ℚ_[p]) (hv : v≠0)
    (hc : v^2=1-D*u^4) (hw : ‖D*u^4‖<1) (hnear : ‖v-1‖<1)
    (r : ℤ) (hr : 1≤r) (hd : v-1=0 ∨ (v-1).valuation=4*r) :
    Padic.addValuation u+((16*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (logarithm p hp D (point D u v hv hc)+u*(Pade21Domains.PJ (v-1)/Pade21Domains.QJ (v-1))) := by
  rw [logarithm_J p hp D u v hv hc hw hnear]
  rw [show -u*JTail318.J p (v-1)+u*(Pade21Domains.PJ (v-1)/Pade21Domains.QJ (v-1))=
    -u*(JTail318.J p (v-1)-Pade21Domains.PJ (v-1)/Pade21Domains.QJ (v-1)) by ring,
    Padic.addValuation.map_mul,Padic.addValuation.map_neg]
  exact add_le_add le_rfl (SeriesEndpoints318.J_precision_zero_or_finite p hp (v-1) r hr hd)

theorem actual_J_linear_error (hp : 19≤p) (D u v : ℚ_[p]) (hv : v≠0)
    (hc : v^2=1-D*u^4) (hw : ‖D*u^4‖<1) (hnear : ‖v-1‖<1)
    (r : ℤ) (hr : 1≤r) (hd : v-1=0 ∨ (v-1).valuation=4*r) :
    Padic.addValuation u+((8*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (logarithm p hp D (point D u v hv hc)+u*(1-(v-1)/5)) := by
  rw [logarithm_J p hp D u v hv hc hw hnear]
  rw [show -u*JTail318.J p (v-1)+u*(1-(v-1)/5)= -u*(JTail318.J p (v-1)-(1-(v-1)/5)) by ring,
    Padic.addValuation.map_mul,Padic.addValuation.map_neg]
  exact add_le_add le_rfl (JLinear318.full_J_linear_precision p hp (v-1) r hr hd)

end
end ActualJLog318
#print axioms ActualJLog318.logarithm_J
#print axioms ActualJLog318.actual_J_pade_error
#print axioms ActualJLog318.actual_J_linear_error
