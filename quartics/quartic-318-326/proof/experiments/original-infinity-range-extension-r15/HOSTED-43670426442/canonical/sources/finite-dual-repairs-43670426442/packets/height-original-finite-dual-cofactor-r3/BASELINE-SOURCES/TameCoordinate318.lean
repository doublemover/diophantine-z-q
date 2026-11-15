module
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic
public section
noncomputable section
open PowerSeries Function Finset
namespace TameCoordinate318
set_option maxHeartbeats 0
variable {k:Type*} [Field k]

@[expose] def sigma (F:k⟦X⟧) (hF:F.constantCoeff=0) : k⟦X⟧→ₐ[k]k⟦X⟧ :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hF)

theorem sigma_apply (F P:k⟦X⟧) (hF:F.constantCoeff=0) : sigma F hF P=P.subst F := by
  exact congrFun (PowerSeries.coe_substAlgHom (HasSubst.of_constantCoeff_zero' hF)) P

theorem constant_derivative (P:k⟦X⟧) : constantCoeff (derivative P)=coeff 1 P := by
  rw [←coeff_zero_eq_constantCoeff,coeff_derivative]
  simp

theorem coeff_one_subst (F P:k⟦X⟧) (hF:F.constantCoeff=0) :
    coeff 1 (P.subst F)=coeff 1 P*coeff 1 F := by
  rw [←constant_derivative,derivative_subst (HasSubst.of_constantCoeff_zero' hF),map_mul]
  have h0:=constantCoeff_subst_of_constantCoeff_zero (R:=k) hF (derivative P)
  change constantCoeff ((derivative P).subst F)=constantCoeff (derivative P) at h0
  rw [h0,constant_derivative,constant_derivative]

theorem sigma_constant (F P:k⟦X⟧) (hF:F.constantCoeff=0) :
    constantCoeff (sigma F hF P)=constantCoeff P := by
  rw [sigma_apply]
  exact constantCoeff_subst_of_constantCoeff_zero (R:=k) hF P

theorem sigma_coeff_one (F P:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F=1) :
    coeff 1 (sigma F hF P)=coeff 1 P := by
  rw [sigma_apply,coeff_one_subst F P hF,h1,mul_one]

@[expose] def orbit (F:k⟦X⟧) (hF:F.constantCoeff=0) (j:ℕ) : k⟦X⟧ :=
  (sigma F hF)^[j] X

theorem orbit_zero (F:k⟦X⟧) (hF:F.constantCoeff=0) : orbit F hF 0=X := rfl

theorem orbit_succ (F:k⟦X⟧) (hF:F.constantCoeff=0) (j:ℕ) :
    orbit F hF (j+1)=sigma F hF (orbit F hF j) := by
  exact Function.iterate_succ_apply' (sigma F hF) j X

theorem orbit_constant (F:k⟦X⟧) (hF:F.constantCoeff=0) (j:ℕ) :
    constantCoeff (orbit F hF j)=0 := by
  induction j with
  | zero => simp [orbit_zero]
  | succ j ih => rw [orbit_succ,sigma_constant,ih]

theorem orbit_coeff_one (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F=1) (j:ℕ) :
    coeff 1 (orbit F hF j)=1 := by
  induction j with
  | zero => simp [orbit_zero]
  | succ j ih => rw [orbit_succ,sigma_coeff_one F _ hF h1,ih]

@[expose] def average (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ) : k⟦X⟧ :=
  (n:k)⁻¹ • ∑j∈Finset.range n,orbit F hF j

theorem average_constant (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ) :
    constantCoeff (average F hF n)=0 := by
  simp [average,orbit_constant]

theorem average_coeff_one (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F=1)
    (n:ℕ) (hn:(n:k)≠0) : coeff 1 (average F hF n)=1 := by
  simp [average,map_smul,orbit_coeff_one F hF h1,hn]

/-- The average of the actual finite substitution orbit is invariant. -/
theorem average_fixed (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ)
    (hperiod:orbit F hF n=X) :
    (average F hF n).subst F=average F hF n := by
  have hsum : (∑j∈range n,orbit F hF (j+1))=∑j∈range n,orbit F hF j := by
    have ht:=Finset.sum_range_succ' (fun j=>orbit F hF j) n
    rw [Finset.sum_range_succ,hperiod,orbit_zero] at ht
    exact add_right_cancel (by simpa only [add_comm] using ht.symm)
  rw [←sigma_apply F (average F hF n) hF]
  simp only [average,map_smul,map_sum,←orbit_succ,hsum]

/-- An invertible formal parameter invariant under substitution forces that
substitution to fix X. This uses the actual compositional inverse. -/
theorem eq_X_of_fixed_parameter (F H:k⟦X⟧) (hF:F.constantCoeff=0)
    (hH:H.constantCoeff=0) (hH1:IsUnit (coeff 1 H)) (hfixed:H.subst F=H) : F=X := by
  have hleft:=PowerSeries.subst_substInvOfIsUnit_left H hH hH1
  have hc:=PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hH)
    (HasSubst.of_constantCoeff_zero' hF) (H.substInvOfIsUnit hH1)
  rw [hleft,PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' hF),hfixed,hleft] at hc
  exact hc

/-- A finite-order formal local coordinate with tangent one is the identity
when its period is invertible in the coefficient field. -/
theorem finite_order_tangent_one (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F=1)
    (n:ℕ) (hn:(n:k)≠0) (hperiod:orbit F hF n=X) : F=X := by
  apply eq_X_of_fixed_parameter F (average F hF n) hF (average_constant F hF n)
  · rw [average_coeff_one F hF h1 n hn]
    exact isUnit_one
  · exact average_fixed F hF n hperiod

/-- Direct formulation using the actual substitution function rather than
its algebra-hom wrapper. -/
theorem finite_substitution_tangent_one (F:k⟦X⟧) (hF:F.constantCoeff=0)
    (h1:coeff 1 F=1) (n:ℕ) (hn:(n:k)≠0)
    (hperiod:(PowerSeries.subst F)^[n] (X:k⟦X⟧)=X) : F=X := by
  apply finite_order_tangent_one F hF h1 n hn
  have he : (sigma F hF : k⟦X⟧→k⟦X⟧)=PowerSeries.subst F := by
    funext P
    exact sigma_apply F P hF
  simpa only [orbit,he] using hperiod

/-- In characteristic zero, every positive finite period is tame. -/
theorem finite_substitution_tangent_one_charZero [CharZero k]
    (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F=1)
    (n:ℕ) (hn:0<n) (hperiod:(PowerSeries.subst F)^[n] (X:k⟦X⟧)=X) : F=X := by
  exact finite_substitution_tangent_one F hF h1 n (Nat.cast_ne_zero.mpr (by omega)) hperiod

end TameCoordinate318
#print axioms TameCoordinate318.average_fixed
#print axioms TameCoordinate318.finite_order_tangent_one
