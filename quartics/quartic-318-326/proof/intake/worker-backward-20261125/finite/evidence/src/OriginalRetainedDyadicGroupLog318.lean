module

public import OriginalDyadicChartLogLimit318
public import OriginalRetainedComplexPointsOverEEquiv318
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

@[expose] public section
noncomputable section

namespace OriginalRetainedDyadicGroupLog318

open AlgebraicGeometry CategoryTheory Filter
open OriginalActualDoublingInverse318 OriginalDyadicChartLogLimit318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (m : V→V→V) {r C : ℝ}

theorem small_pair_fits (hr : 0<r) (hC : 0≤C) (small : C*r≤1/3)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2)
    (x y : V) (hx : ‖x‖≤r/4) (hy : ‖y‖≤r/4) :
    ‖m x y‖≤r := by
  have thin : r/4≤r := by linarith
  have mx : max ‖x‖ ‖y‖≤r/4 := max_le hx hy
  have mx0 : 0≤max ‖x‖ ‖y‖ := (norm_nonneg x).trans (le_max_left _ _)
  have hm : (max ‖x‖ ‖y‖)^2≤(r/4)^2 := pow_le_pow_left₀ mx0 mx _
  have hq : C*(r/4)^2≤r/48 := by
    calc
      _ = (C*r)*(r/16) := by ring
      _ ≤ (1/3:ℝ)*(r/16) := mul_le_mul_of_nonneg_right small (by linarith)
      _ = _ := by ring
  calc
    ‖m x y‖ = ‖(m x y-(x+y))+(x+y)‖ := by rw [sub_add_cancel]
    _ ≤ ‖m x y-(x+y)‖+‖x+y‖ := norm_add_le _ _
    _ ≤ C*(max ‖x‖ ‖y‖)^2+(‖x‖+‖y‖) :=
      add_le_add (quad x y (hx.trans thin) (hy.trans thin)) (norm_add_le _ _)
    _ ≤ C*(r/4)^2+(r/4+r/4) := add_le_add (mul_le_mul_of_nonneg_left hm hC) (add_le_add hx hy)
    _ ≤ r := by linarith

section WholeOriginalPoints

local notation "Tc" => Spec (CommRingCat.of ℂ)

variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : Tc ⟶ E)
variable [MonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]
variable [IsCommMonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]

abbrev Point := Over.mk (𝟙 Tc) ⟶ OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33)

variable (pt : V → Point a P33 σ) {chart : ℝ}

variable (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
variable (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
variable (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)

variable (H : HalfOn m r C)
variable (hr : 0<r) (hC : 0≤C) (small : C*r≤1/3)
variable (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2)

/-- The point operation here is definitionally the group law installed on
the retained original fibre in Spec(C)/Y. Half uniqueness is only used
inside the one valid r-ball; the larger chart is used for injectivity. -/
theorem half_reads_original_product (x y : V) (hx : ‖x‖≤r/4) (hy : ‖y‖≤r/4) :
    H.s (m x y)=m (H.s x) (H.s y) := by
  have thin : r/4≤r := by linarith
  have hxr := hx.trans thin
  have hyr := hy.trans thin
  have hxs : ‖H.s x‖≤r/4 := (walk_mem H x hxr 1).trans hx
  have hys : ‖H.s y‖≤r/4 := (walk_mem H y hyr 1).trans hy
  have hm : ‖m x y‖≤r := small_pair_fits m hr hC small quad x y hx hy
  have hms : ‖m (H.s x) (H.s y)‖≤r :=
    small_pair_fits m hr hC small quad _ _ hxs hys
  let z := m (H.s x) (H.s y)
  have hinside : ‖m z z‖≤chart := fit z z hms hms
  have hz : m z z=m x y := inj _ _ hinside (fit x y hxr hyr) (by
    calc
      pt (m z z) = (pt (H.s x)*pt (H.s y))*(pt (H.s x)*pt (H.s y)) := by
        rw [law z z hms hms]
        unfold z
        rw [law (H.s x) (H.s y) (hxs.trans thin) (hys.trans thin)]
      _ = (pt (H.s x)*pt (H.s x))*(pt (H.s y)*pt (H.s y)) := by ac_rfl
      _ = pt (m (H.s x) (H.s x))*pt (m (H.s y) (H.s y)) := by
        rw [law (H.s x) (H.s x) (hxs.trans thin) (hxs.trans thin),
          law (H.s y) (H.s y) (hys.trans thin) (hys.trans thin)]
      _ = pt (m x y) := by rw [H.halves x hxr,H.halves y hyr,law x y hxr hyr])
  exact (H.unique (m x y) z hm hms hz).symm

theorem walk_reads_original_product (x y : V) (hx : ‖x‖≤r/4) (hy : ‖y‖≤r/4) (n : ℕ) :
    walk H.s n (m x y)=m (walk H.s n x) (walk H.s n y) := by
  have thin : r/4≤r := by linarith
  induction n with
  | zero => rfl
  | succ n ih =>
    change H.s (walk H.s n (m x y)) =
      m (H.s (walk H.s n x)) (H.s (walk H.s n y))
    rw [ih]
    exact half_reads_original_product m a P33 σ pt fit inj law H hr hC small quad
      _ _ ((walk_mem H x (hx.trans thin) n).trans hx)
      ((walk_mem H y (hy.trans thin) n).trans hy)

theorem actual_log_respects_original_law
    (l : V→V) (hl : ∀ x, ‖x‖≤r → Tendsto (fun n=>approximate H n x) atTop (𝓝 (l x)))
    (x y : V) (hx : ‖x‖≤r/4) (hy : ‖y‖≤r/4) :
    l (m x y)=l x+l y := by
  have thin : r/4≤r := by linarith
  have hxr := hx.trans thin
  have hyr := hy.trans thin
  have hxy := small_pair_fits m hr hC small quad x y hx hy
  have hn (n : ℕ) :
      ‖approximate H n (m x y)-(approximate H n x+approximate H n y)‖ ≤
        (C*(max ‖x‖ ‖y‖)^2)*gain^n := by
    unfold approximate
    rw [walk_reads_original_product m a P33 σ pt fit inj law H hr hC small quad x y hx hy,
      ←smul_add,←smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : 0≤(2:ℝ)) _)]
    have nx := (walk_mem H x hxr n).trans hxr
    have ny := (walk_mem H y hyr n).trans hyr
    have hp : max ‖walk H.s n x‖ ‖walk H.s n y‖ ≤ kappa^n*max ‖x‖ ‖y‖ := by
      apply max_le
      · exact (walk_norm H x hxr n).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg kappa_nonneg _))
      · exact (walk_norm H y hyr n).trans
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg kappa_nonneg _))
    have hp0 : 0≤max ‖walk H.s n x‖ ‖walk H.s n y‖ :=
      (norm_nonneg _).trans (le_max_left _ _)
    calc
      _ ≤ (2:ℝ)^n*(C*(max ‖walk H.s n x‖ ‖walk H.s n y‖)^2) :=
        mul_le_mul_of_nonneg_left (quad _ _ nx ny) (pow_nonneg (by norm_num) _)
      _ ≤ (2:ℝ)^n*(C*(kappa^n*max ‖x‖ ‖y‖)^2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp _) hC)
          (pow_nonneg (by norm_num) _)
      _ = _ := by unfold gain; rw [mul_pow,pow_mul]; ring
  have hz := (hl (m x y) hxy).sub ((hl x hxr).add (hl y hyr))
  have lim : Tendsto (fun n : ℕ => (C*(max ‖x‖ ‖y‖)^2)*gain^n) atTop (𝓝 0) := by
    have t := (tendsto_pow_atTop_nhds_zero_of_lt_one gain_nonneg gain_lt_one).const_mul
      (C*(max ‖x‖ ‖y‖)^2)
    rw [mul_zero] at t
    exact t
  exact sub_eq_zero.1 (tendsto_nhds_unique hz (squeeze_zero_norm hn lim))

end WholeOriginalPoints

/-- Once the actual dyadic limit has its proved displacement estimate,
one use of the same centered contraction gives the genuine local
inverse without an independent inverse-function chart. -/
theorem log_local_inverse [CompleteSpace V] (l : V→V) (l0 : l 0=0) {ρ : ℝ}
    (hρ : 0<ρ)
    (loc : ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ → ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖) :
    ∃ λ : V→V,
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ w z, ‖w‖≤ρ/2 → ‖z‖≤ρ → l z=w → z=λ w) := by
  let F := fun w z => w-(l z-z)
  have at0 (w : V) (hw : ‖w‖≤ρ/2) : ‖F w 0‖≤(1-(1/2:ℝ))*ρ := by
    change ‖w-(l 0-0)‖≤(1-(1/2:ℝ))*ρ
    rw [l0,sub_zero,sub_zero]
    linarith
  have lip (w : V) (_ : ‖w‖≤ρ/2) (x y : V) (hx : ‖x‖≤ρ) (hy : ‖y‖≤ρ) :
      ‖F w x-F w y‖≤(1/2:ℝ)*‖x-y‖ := by
    change ‖(w-(l x-x))-(w-(l y-y))‖≤_
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
    exact loc x y hx hy
  have eq (w z : V) : z-F w z=0 ↔ l z=w := by
    have h : z-F w z=l z-w := by dsimp only [F]; abel
    rw [h,sub_eq_zero]
  obtain ⟨λ,hλ,hunique⟩ := OriginalCenteredAnalyticEquation318.zeroChart F
    hρ (by norm_num : 0≤(1/2:ℝ)) (by norm_num) at0 lip
  exact ⟨λ,fun w hw => ⟨(hλ w hw).1,(eq w (λ w)).1 (hλ w hw).2⟩,
    fun w z hw hz h => (hunique w z hw hz).1 ((eq w z).2 h)⟩


section WholeLogProducer

local notation "Tc" => Spec (CommRingCat.of ℂ)
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : Tc ⟶ E)
variable [MonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]
variable [IsCommMonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]
variable (pt : V→Point a P33 σ) {chart : ℝ}

variable (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
variable (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
variable (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)

/-- Produce the centered local log and an actual inverse domain for
the installed original operation. No closedness, coordinate-rescaling,
or independent period map is used. The norm estimates refer to the
same fixed chart read which occurs in fit/inj/law. -/
theorem exists_original_local_log_with_region [CompleteSpace V]
    (hr : 0<r) (hC : 0≤C) (small : C*r≤1/3) (zero : m 0 0=0)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (l λ : V→V), 0<ρ ∧ ρ≤r/4 ∧ l 0=0 ∧
      (∀ x, ‖x‖≤r → ‖l x-x‖≤(2*halfErrorConstant C)*‖x‖^2/(1-gain)) ∧
      (∀ x y, ‖x‖≤r/4 → ‖y‖≤r/4 → l (m x y)=l x+l y) ∧
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ w z, ‖w‖≤ρ/2 → ‖z‖≤ρ → l z=w → z=λ w) ∧
      (∀ x y, ‖x‖≤ρ → ‖y‖≤ρ → ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖) := by
  obtain ⟨H⟩ := exists_half m hr hC small zero defectLip
  obtain ⟨l,hl,l0,lLip⟩ := exists_log H hC hr.le
  let K := halfErrorConstant C
  have hK : 0≤K := mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg _)
  have qgap : 0<1-gain := sub_pos.2 gain_lt_one
  let ρ := min (r/4) ((1-gain)/(4*(K+1)))
  have ρpos : 0<ρ := lt_min (by linarith) (div_pos qgap (by linarith))
  have hρr : ρ≤r/4 := min_le_left _ _
  have hρr' : ρ≤r := hρr.trans (by linarith)
  have hρK : ρ*(4*(K+1))≤1-gain :=
    (le_div_iff₀ (by linarith : 0<4*(K+1))).1 (min_le_right _ _)
  have hcoeff : (2*K*ρ)/(1-gain)≤1/2 := by
    apply (div_le_iff₀ qgap).2
    nlinarith only [hρK,ρpos.le]
  have ηlip (x y : V) (hx : ‖x‖≤ρ) (hy : ‖y‖≤ρ) :
      ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖ := by
    calc
      _ ≤ (2*K*ρ*‖x-y‖)/(1-gain) := lLip ρ ρpos.le hρr' x y hx hy
      _ = ((2*K*ρ)/(1-gain))*‖x-y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  obtain ⟨λ,hλ₁,hλ₂⟩ := log_local_inverse l l0 ρpos ηlip
  refine ⟨ρ,l,λ,ρpos,hρr,l0,?_,?_,hλ₁,hλ₂,ηlip⟩
  · intro x hx
    have h := lLip ‖x‖ (norm_nonneg x) hx x 0 le_rfl
      (by rw [norm_zero]; exact norm_nonneg x)
    rw [l0,sub_zero,sub_zero,sub_zero] at h
    calc
      _ ≤ (2*halfErrorConstant C*‖x‖*‖x‖)/(1-gain) := h
      _ = _ := by ring
  · exact actual_log_respects_original_law m a P33 σ pt fit inj law H hr hC small quad l hl

/-- Legacy proposition retained; the common choices are made in the
stronger original producer above. -/
theorem exists_original_local_log [CompleteSpace V]
    (hr : 0<r) (hC : 0≤C) (small : C*r≤1/3) (zero : m 0 0=0)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (l λ : V→V), 0<ρ ∧ ρ≤r/4 ∧ l 0=0 ∧
      (∀ x, ‖x‖≤r → ‖l x-x‖≤(2*halfErrorConstant C)*‖x‖^2/(1-gain)) ∧
      (∀ x y, ‖x‖≤r/4 → ‖y‖≤r/4 → l (m x y)=l x+l y) ∧
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ w z, ‖w‖≤ρ/2 → ‖z‖≤ρ → l z=w → z=λ w) := by
  obtain ⟨ρ,l,λ,hρ,hρr,l0,along,add,read,unique,_⟩ :=
    exists_original_local_log_with_region m a P33 σ pt fit inj law hr hC small zero defectLip quad
  exact ⟨ρ,l,λ,hρ,hρr,l0,along,add,read,unique⟩

end WholeLogProducer

end OriginalRetainedDyadicGroupLog318
