module
public import ActualLogHom318
public import CanonicalChart318
public section
namespace ActualLogMembership318
open ClosedActualLog318 ActualLogHom318 ReciprocalDouble318 WeierstrassCurve.Affine
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _
set_option maxHeartbeats 0

/-- Concrete source-to-subgroup interface. A local affine point with small
formal parameter is on the actual analytic logarithm subgroup; no reciprocal
square root of 1/x is assumed. -/
theorem affine_mem (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (x y : ℚ_[p]) (hx : x≠0) (hy : y≠0) (hc : y^2=x^3-D*x)
    (h : (E D).Nonsingular x y) (hw : ‖D/x^2‖<1) (hz : ‖-x/y‖≤‖(p:ℚ_[p])‖) :
    Point.some x y h ∈ formalSubgroup p hp D hD := by
  let v:=CanonicalRoot318.root p hp (D/x^2)
  have hvs : v^2=1-D/x^2 ∧ ‖v-1‖<1 := CanonicalRoot318.root_spec p hp _ hw
  have hvn : ‖v‖=1 := by
    simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right
      (show ‖v-1‖<‖(1:ℚ_[p])‖ by simpa only [norm_one] using hvs.2)
  have hv0 : v≠0 := by intro he; rw [he,norm_zero] at hvn; exact zero_ne_one hvn
  let u:=x*v/y
  have hcU := CanonicalChart318.reciprocal_coordinates D x y v hx hy hv0 hc hvs.1
  change u≠0 ∧ 1/u^2=x ∧ v/u^3=y ∧ v^2=1-D*u^4 at hcU
  have hun : ‖u‖=‖-x/y‖ := by dsimp [u]; rw [norm_div,norm_mul,hvn,mul_one,norm_div,norm_neg]
  have hp0 : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hnorm : ‖u/(p:ℚ_[p])‖≤1 := by
    rw [norm_div]
    apply (div_le_one (norm_pos_iff.mpr hp0)).mpr
    rw [hun]; exact hz
  let t : ℤ_[p] := (u/(p:ℚ_[p])).lift hnorm
  have hut : U p t=u := by
    dsimp [U,t]
    field_simp [hp0]
  have harg : D*(U p t)^4=D/x^2 := by
    rw [hut,←hcU.2.1]
    field_simp
  have hvt : V p hp D hD t=v := by rw [root_binding,harg]
  refine ⟨t,?_⟩
  simp only [chart,point,hut,hvt,dite_eq_right hcU.1,hcU.2.1,hcU.2.2.1]

end
end ActualLogMembership318
#print axioms ActualLogMembership318.affine_mem
