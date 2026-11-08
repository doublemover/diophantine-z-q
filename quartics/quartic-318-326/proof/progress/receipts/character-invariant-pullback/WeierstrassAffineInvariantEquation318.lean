module
public import WeierstrassFiniteDifferentialEquality318
public section
noncomputable section
namespace WeierstrassAffineInvariantEquation318
open AlgebraicGeometry CategoryTheory KaehlerDifferential ShortAffineJacobian318
open WeierstrassAffineInvariant318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] (A B:R)

/-- The normalized invariant has 2y times it equal to dx also on the
x-Jacobian chart, where y itself may vanish. -/
theorem x_equation :
    algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 0) (2*y A B) •
      FiniteInvariantDifferential318.xForm A B=
        D R (WeierstrassKaehler318.AffineChart A B 0)
          (algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 0) (x A B)) := by
  let inv:=IsLocalization.Away.invSelf (S:=WeierstrassKaehler318.AffineChart A B 0)
    (presentation A B 0).jacobian
  have h:=congrArg (AlgHomDifferential318.map (chartMap A B 0))
    (FiniteInvariantDifferential318.differentiated_relation A B)
  simp only [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,map_neg] at h
  have hh:=congrArg (fun ω:KaehlerDifferential R (WeierstrassKaehler318.AffineChart A B 0)=>inv • ω) h
  rw [smul_smul,smul_smul] at hh
  have hi:inv * algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 0)
      (presentation A B 0).jacobian=1:=by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  change (inv * algebraMap _ _ (presentation A B 0).jacobian) • _=
    (inv * -algebraMap _ _ (presentation A B 1).jacobian) • _ at hh
  rw [hi,one_smul,jacobian_y] at hh
  rw [FiniteInvariantDifferential318.xForm,smul_smul]
  exact (congrArg (fun a:WeierstrassKaehler318.AffineChart A B 0=>a •
      D R _ (algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 0) (y A B)))
    (show algebraMap _ _ (2*y A B) * -inv=inv * -algebraMap _ _ (2*y A B) by ring)).trans hh.symm

theorem y_equation :
    algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 1) (2*y A B) •
      InvariantChartForms318.finite A B=
        D R (WeierstrassKaehler318.AffineChart A B 1)
          (algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 1) (x A B)) := by
  rw [InvariantChartForms318.finite,smul_smul,←jacobian_y,
    IsLocalization.Away.mul_invSelf,one_smul]

/-- Denominator-free normalization on the ENTIRE finite coordinate ring.
The two full Jacobian opens prove this across every finite branch point. -/
theorem equation (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (2*y A B) • form A B hD=D R (Ring A B) (x A B) := by
  apply WeierstrassFiniteDifferentialEquality318.eq_of_charts A B hD
  intro i
  rw [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D]
  fin_cases i
  · change algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 0) (2*y A B) •
      AlgHomDifferential318.map (chartMap A B 0) (form A B hD)=
        D R (WeierstrassKaehler318.AffineChart A B 0) (algebraMap (Ring A B) _ (x A B))
    rw [form_x]
    exact x_equation A B
  · change algebraMap (Ring A B) (WeierstrassKaehler318.AffineChart A B 1) (2*y A B) •
      AlgHomDifferential318.map (chartMap A B 1) (form A B hD)=
        D R (WeierstrassKaehler318.AffineChart A B 1) (algebraMap (Ring A B) _ (x A B))
    rw [form_y]
    exact y_equation A B
end WeierstrassAffineInvariantEquation318
