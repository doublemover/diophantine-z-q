module

public import OriginalCenteredAnalyticEquation318
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace OriginalActualDoublingInverse318

open Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def defect (m : V → V → V) (x : V) : V :=
  m x x - (2:ℝ) • x

def halfResidual (m : V → V → V) (z x : V) : V :=
  (1/2:ℝ) • (z-defect m x)

theorem residual_iff_doubling (m : V → V → V) (z x : V) :
    x - halfResidual m z x=0 ↔ m x x=z := by
  constructor
  · intro h
    have h' := congrArg (fun y : V => (2:ℝ) • y) (sub_eq_zero.1 h)
    change (2:ℝ) • x = (2:ℝ) • ((1/2:ℝ) • (z-defect m x)) at h'
    rw [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] at h'
    calc
      m x x = defect m x+(2:ℝ) • x := (sub_add_cancel _ _).symm
      _ = defect m x+(z-defect m x) := congrArg ((defect m x)+·) h'
      _ = z := by rw [add_comm,sub_add_cancel]
  · intro h
    apply sub_eq_zero.2
    unfold halfResidual defect
    rw [h,sub_sub_cancel,smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul]

theorem residual_move (m : V → V → V) (z z' x : V) :
    ‖halfResidual m z x-halfResidual m z' x‖ = (1/2:ℝ)*‖z-z'‖ := by
  unfold halfResidual
  rw [←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs]
  norm_num

theorem residual_in_x (m : V → V → V) (z x x' : V) :
    ‖halfResidual m z x-halfResidual m z x'‖ =
      (1/2:ℝ)*‖defect m x-defect m x'‖ := by
  unfold halfResidual
  rw [←smul_sub,sub_sub_sub_cancel_left,norm_smul,Real.norm_eq_abs,norm_sub_rev]
  norm_num

def kappa : ℝ := 3/5

theorem kappa_nonneg : 0 ≤ kappa := by norm_num [kappa]
theorem kappa_lt_one : kappa < 1 := by norm_num [kappa]

/-- This data is intrinsic to the specified multiplication in the fixed
chart. Exact uniqueness is needed to use the *true* commutative law
to compare the local half of a product with the product of its halves. -/
structure HalfOn (m : V → V → V) (r C : ℝ) where
  s : V → V
  centre : s 0=0
  bound : ∀ z, ‖z‖≤r → ‖s z‖≤kappa*‖z‖
  halves : ∀ z, ‖z‖≤r → m (s z) (s z)=z
  unique : ∀ z x, ‖z‖≤r → ‖x‖≤r → m x x=z → x=s z
  lip : ∀ z z', ‖z‖≤r → ‖z'‖≤r → ‖s z-s z'‖≤kappa*‖z-z'‖
  errorLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ z z', ‖z‖≤ρ → ‖z'‖≤ρ →
    ‖(s z-(1/2:ℝ)•z)-(s z'-(1/2:ℝ)•z')‖ ≤
      ((C/2)*kappa^2)*ρ*‖z-z'‖

/-- Invert exactly the chosen local [2] throughout the one closed ball.
The defect estimate is required on every smaller centered ball; the
real coefficient is fixed at one half, not an Hodge normalization. -/
theorem exists_half [CompleteSpace V] (m : V → V → V)
    {r C : ℝ} (hr : 0<r) (hC : 0≤C) (small : C*r≤1/3)
    (zero : m 0 0=0)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖) :
    Nonempty (HalfOn m r C) := by
  have e0 : defect m 0=0 := by simp [defect,zero]
  have ball0 : ‖(0:V)‖≤r := by simpa only [norm_zero] using hr.le
  have hz : ∀ z : V, ‖z‖≤r →
      ‖halfResidual m z 0‖≤(1-(1/6:ℝ))*r := by
    intro z hz
    rw [halfResidual,e0,sub_zero,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    linarith
  have hLip : ∀ z : V, ‖z‖≤r → ∀ x y, ‖x‖≤r → ‖y‖≤r →
      ‖halfResidual m z x-halfResidual m z y‖≤(1/6:ℝ)*‖x-y‖ := by
    intro z _ x y hx hy
    rw [residual_in_x]
    calc
      _ ≤ (1/2:ℝ)*(C*r*‖x-y‖) :=
        mul_le_mul_of_nonneg_left (defectLip r hr.le le_rfl x y hx hy) (by norm_num)
      _ = ((1/2:ℝ)*(C*r))*‖x-y‖ := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  obtain ⟨s,hs,huniq⟩ := OriginalCenteredAnalyticEquation318.zeroChart
    (halfResidual m) hr (by norm_num : 0≤(1/6:ℝ)) (by norm_num) hz hLip
  have s0 : s 0=0 := ((huniq 0 0 ball0 ball0).1 ((residual_iff_doubling m 0 0).2 zero)).symm
  have hsLip : ∀ z z', ‖z‖≤r → ‖z'‖≤r → ‖s z-s z'‖≤kappa*‖z-z'‖ := by
    intro z z' hz hz'
    have hm : ‖halfResidual m z (s z)-halfResidual m z' (s z)‖≤(1/2:ℝ)*‖z-z'‖ :=
      (residual_move m z z' (s z)).le
    calc
      _ ≤ (1/2:ℝ)*‖z-z'‖/(1-(1/6:ℝ)) :=
        OriginalCenteredAnalyticEquation318.zeroChart_parameter
          (halfResidual m) z z' (s z) (s z') (by norm_num)
          (hs z hz).2 (hs z' hz').2 hm (hLip z' hz' _ _ (hs z hz).1 (hs z' hz').1)
      _ = _ := by unfold kappa; ring
  have shrink : ∀ z, ‖z‖≤r → ‖s z‖≤kappa*‖z‖ := by
    intro z hz
    simpa only [s0,sub_zero] using hsLip z 0 hz ball0
  have herror (z : V) (hz : ‖z‖≤r) :
      s z-(1/2:ℝ)•z = -(1/2:ℝ) • defect m (s z) := by
    have he := sub_eq_zero.1 (hs z hz).2
    calc
      _ = ((1/2:ℝ) • (z-defect m (s z)))-(1/2:ℝ)•z :=
        congrArg (fun w : V => w-(1/2:ℝ)•z) he
      _ = _ := by rw [smul_sub,sub_right_comm,sub_self,zero_sub,neg_smul]
  refine ⟨⟨s,s0,shrink,?_,?_,hsLip,?_⟩⟩
  · intro z hz
    exact (residual_iff_doubling m z (s z)).1 (hs z hz).2
  · intro z x hz hx he
    exact (huniq z x hz hx).1 ((residual_iff_doubling m z x).2 he)
  · intro ρ hρ hρr z z' hz hz'
    have kpos : 0≤kappa*ρ := mul_nonneg kappa_nonneg hρ
    have kρ : kappa*ρ≤r := (mul_le_of_le_one_left hρ kappa_lt_one.le).trans hρr
    have hsz : ‖s z‖≤kappa*ρ :=
      (shrink z (hz.trans hρr)).trans (mul_le_mul_of_nonneg_left hz kappa_nonneg)
    have hsz' : ‖s z'‖≤kappa*ρ :=
      (shrink z' (hz'.trans hρr)).trans (mul_le_mul_of_nonneg_left hz' kappa_nonneg)
    rw [herror z (hz.trans hρr),herror z' (hz'.trans hρr),←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_nonpos (by norm_num : -(1/2:ℝ)≤0),neg_neg]
    calc
      _ ≤ (1/2:ℝ)*(C*(kappa*ρ)*‖s z-s z'‖) :=
        mul_le_mul_of_nonneg_left (defectLip (kappa*ρ) kpos kρ _ _ hsz hsz') (by norm_num)
      _ ≤ (1/2:ℝ)*(C*(kappa*ρ)*(kappa*‖z-z'‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hsLip z z' (hz.trans hρr) (hz'.trans hρr))
            (mul_nonneg hC kpos)) (by norm_num)
      _ = _ := by ring

end OriginalActualDoublingInverse318
