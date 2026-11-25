module

public import OriginalActualDoublingInverse318
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section

namespace OriginalDyadicChartLogLimit318

open Filter OriginalActualDoublingInverse318
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def walk (s : V → V) : ℕ → V → V
  | 0, x => x
  | n+1, x => s (walk s n x)

variable {m : V → V → V} {r C : ℝ} (H : HalfOn m r C)

theorem walk_zero : ∀ n, walk H.s n 0=0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [walk,ih,H.centre]

theorem walk_norm (x : V) (hx : ‖x‖≤r) (n : ℕ) :
    ‖walk H.s n x‖≤kappa^n*‖x‖ := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    have hk : kappa^n≤1 := pow_le_one₀ kappa_nonneg kappa_lt_one.le
    have hmem := ih.trans ((mul_le_of_le_one_left (norm_nonneg x) hk).trans hx)
    calc
      ‖walk H.s (n+1) x‖ ≤ kappa*‖walk H.s n x‖ := H.bound _ hmem
      _ ≤ kappa*(kappa^n*‖x‖) := mul_le_mul_of_nonneg_left ih kappa_nonneg
      _ = _ := by rw [pow_succ]; ring

theorem walk_mem (x : V) (hx : ‖x‖≤r) (n : ℕ) :
    ‖walk H.s n x‖≤‖x‖ :=
  (walk_norm H x hx n).trans
    (mul_le_of_le_one_left (norm_nonneg x) (pow_le_one₀ kappa_nonneg kappa_lt_one.le))

theorem walk_lip (x y : V) (hx : ‖x‖≤r) (hy : ‖y‖≤r) (n : ℕ) :
    ‖walk H.s n x-walk H.s n y‖≤kappa^n*‖x-y‖ := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    calc
      ‖walk H.s (n+1) x-walk H.s (n+1) y‖ ≤
          kappa*‖walk H.s n x-walk H.s n y‖ :=
        H.lip _ _ ((walk_mem H x hx n).trans hx) ((walk_mem H y hy n).trans hy)
      _ ≤ kappa*(kappa^n*‖x-y‖) := mul_le_mul_of_nonneg_left ih kappa_nonneg
      _ = _ := by rw [pow_succ]; ring

def err (x : V) : V := H.s x-(1/2:ℝ)•x
def approximate (n : ℕ) (x : V) : V := (2:ℝ)^n • walk H.s n x

def gain : ℝ := 2*kappa^2
def halfErrorConstant (C : ℝ) : ℝ := (C/2)*kappa^2

theorem gain_nonneg : 0≤gain := by norm_num [gain,kappa]
theorem gain_lt_one : gain<1 := by norm_num [gain,kappa]

theorem gain_read : gain=(18/25:ℝ) := by norm_num [gain,kappa]

theorem approximate_zero (x : V) : approximate H 0 x=x := by simp [approximate,walk]
theorem approximate_at_centre (n : ℕ) : approximate H n 0=0 := by
  rw [approximate,walk_zero,smul_zero]

theorem increment (n : ℕ) (x : V) :
    approximate H (n+1) x-approximate H n x=(2:ℝ)^(n+1) • err H (walk H.s n x) := by
  unfold approximate err
  rw [walk,smul_sub,smul_smul]
  have e : (2:ℝ)^(n+1)*(1/2:ℝ)=(2:ℝ)^n := by rw [pow_succ]; ring
  rw [e]

theorem increment_lip (hC : 0≤C) (ρ : ℝ) (hρ : 0≤ρ) (hρr : ρ≤r)
    (x y : V) (hx : ‖x‖≤ρ) (hy : ‖y‖≤ρ) (n : ℕ) :
    ‖(approximate H (n+1) x-approximate H n x)-
        (approximate H (n+1) y-approximate H n y)‖ ≤
      (2*halfErrorConstant C)*ρ*‖x-y‖*gain^n := by
  let ρn := kappa^n*ρ
  have hn : 0≤ρn := mul_nonneg (pow_nonneg kappa_nonneg _) hρ
  have hnr : ρn≤r :=
    (mul_le_of_le_one_left hρ (pow_le_one₀ kappa_nonneg kappa_lt_one.le)).trans hρr
  have hnX : ‖walk H.s n x‖≤ρn := (walk_norm H x (hx.trans hρr) n).trans
    (mul_le_mul_of_nonneg_left hx (pow_nonneg kappa_nonneg _))
  have hnY : ‖walk H.s n y‖≤ρn := (walk_norm H y (hy.trans hρr) n).trans
    (mul_le_mul_of_nonneg_left hy (pow_nonneg kappa_nonneg _))
  have ht : 0≤halfErrorConstant C*ρn := mul_nonneg
    (mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg _)) hn
  rw [increment H n x,increment H n y,←smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : 0≤(2:ℝ)) _)]
  calc
    _ ≤ (2:ℝ)^(n+1) *
      (halfErrorConstant C*ρn*‖walk H.s n x-walk H.s n y‖) :=
      mul_le_mul_of_nonneg_left (H.errorLip _ hn hnr _ _ hnX hnY) (pow_nonneg (by norm_num : 0≤(2:ℝ)) _)
    _ ≤ (2:ℝ)^(n+1) * (halfErrorConstant C*ρn*(kappa^n*‖x-y‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (walk_lip H x y (hx.trans hρr) (hy.trans hρr) n) ht)
        (pow_nonneg (by norm_num : 0≤(2:ℝ)) _)
    _ = _ := by
      unfold gain
      rw [mul_pow,pow_mul,pow_succ (2:ℝ)]
      dsimp only [ρn]
      ring

theorem approximate_cauchy (hC : 0≤C) (x : V) (hx : ‖x‖≤r) :
    CauchySeq (fun n => approximate H n x) := by
  apply cauchySeq_of_le_geometric gain ((2*halfErrorConstant C)*‖x‖^2) gain_lt_one
  intro n
  have h := increment_lip H hC ‖x‖ (norm_nonneg x) hx
    x 0 le_rfl (by rw [norm_zero]; exact norm_nonneg x) n
  rw [approximate_at_centre H (n+1),approximate_at_centre H n,sub_self,sub_zero,sub_zero] at h
  rw [dist_eq_norm,norm_sub_rev]
  calc
    _ ≤ (2*halfErrorConstant C)*‖x‖*‖x‖*gain^n := h
    _ = _ := by ring

/-- A norm bound for the finite normalized approximants, already
uniform on each nested ball. No integration or global holomorphy
enters the construction. -/
theorem approximate_displacement_lip (hC : 0≤C) (ρ : ℝ)
    (hρ : 0≤ρ) (hρr : ρ≤r) (x y : V) (hx : ‖x‖≤ρ) (hy : ‖y‖≤ρ) (n : ℕ) :
    ‖(approximate H n x-x)-(approximate H n y-y)‖ ≤
      ((2*halfErrorConstant C)*ρ*‖x-y‖)*(1-gain^n)/(1-gain) := by
  let B := (2*halfErrorConstant C)*ρ*‖x-y‖
  induction n with
  | zero => simp [approximate_zero]
  | succ n ih =>
    let D := (approximate H n x-x)-(approximate H n y-y)
    let E := (approximate H (n+1) x-approximate H n x)-
      (approximate H (n+1) y-approximate H n y)
    have e : (approximate H (n+1) x-x)-(approximate H (n+1) y-y)=D+E := by
      dsimp only [D,E]
      abel
    rw [e]
    calc
      ‖D+E‖ ≤ ‖D‖+‖E‖ := norm_add_le _ _
      _ ≤ B*(1-gain^n)/(1-gain)+B*gain^n :=
        add_le_add ih (increment_lip H hC ρ hρ hρr x y hx hy n)
      _ = _ := by
        have nz : 1-gain≠0 := ne_of_gt (sub_pos.2 gain_lt_one)
        rw [pow_succ]
        change B*(1-gain^n)/(1-gain)+B*gain^n =
          B*(1-gain^n*gain)/(1-gain)
        apply (eq_div_iff nz).2
        rw [add_mul,div_mul_cancel₀ _ nz]
        ring

theorem exists_log [CompleteSpace V] (hC : 0≤C) (hr : 0≤r) :
    ∃ l : V→V,
      (∀ x, ‖x‖≤r → Tendsto (fun n => approximate H n x) atTop (𝓝 (l x))) ∧
      l 0=0 ∧
      (∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
        ‖(l x-x)-(l y-y)‖ ≤ ((2*halfErrorConstant C)*ρ*‖x-y‖)/(1-gain)) := by
  classical
  have h : ∀ x, ‖x‖≤r → ∃ w, Tendsto (fun n => approximate H n x) atTop (𝓝 w) :=
    fun x hx => cauchySeq_tendsto_of_complete (approximate_cauchy H hC x hx)
  let l : V→V := fun x => if hx : ‖x‖≤r then Classical.choose (h x hx) else 0
  have hl : ∀ x, ‖x‖≤r → Tendsto (fun n => approximate H n x) atTop (𝓝 (l x)) := by
    intro x hx
    simpa only [l,dite_eq_left hx] using Classical.choose_spec (h x hx)
  have h0 : l 0=0 :=
    tendsto_nhds_unique
      (hl 0 (by simpa only [norm_zero] using hr))
      (by simpa only [approximate_at_centre] using tendsto_const_nhds)
  refine ⟨l,hl,h0,?_⟩
  intro ρ hρ hρr x y hx hy
  have hdx := (hl x (hx.trans hρr)).sub
    (show Tendsto (fun _ : ℕ => x) atTop (𝓝 x) from tendsto_const_nhds)
  have hdy := (hl y (hy.trans hρr)).sub
    (show Tendsto (fun _ : ℕ => y) atTop (𝓝 y) from tendsto_const_nhds)
  have hnorm := continuous_norm.continuousAt.tendsto.comp (hdx.sub hdy)
  refine le_of_tendsto' hnorm (fun n => (approximate_displacement_lip H hC ρ hρ hρr x y hx hy n).trans ?_)
  have B0 : 0≤(2*halfErrorConstant C)*ρ*‖x-y‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg _))) hρ) (norm_nonneg _)
  apply div_le_div_of_nonneg_right _ (sub_pos.2 gain_lt_one).le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (sub_le_self 1 (pow_nonneg gain_nonneg n)) B0

end OriginalDyadicChartLogLimit318
