module

public import OriginalRetainedDyadicGroupLog318
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section
noncomputable section

namespace OriginalRetainedDyadicInverseRay318

open Filter AlgebraicGeometry CategoryTheory
open OriginalRetainedDyadicGroupLog318 OriginalActualDoublingInverse318 OriginalDyadicChartLogLimit318
open scoped Topology CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type*} [NormedAddCommGroup V]

section ExactInverse

variable (l λ : V→V) {ρ B : ℝ}
variable (hρ : 0<ρ) (hB : 0≤B) (small : B*ρ≤1/2)
variable (direct : ∀ z, ‖z‖≤ρ → ‖l z-z‖≤B*‖z‖^2)
variable (read : ∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w)

include hB small direct read in
theorem inverse_norm (w : V) (hw : ‖w‖≤ρ/2) : ‖λ w‖≤2*‖w‖ := by
  have hm := (read w hw).1
  have he := (read w hw).2
  have ha := direct (λ w) hm
  have hb : B*‖λ w‖≤1/2 :=
    (mul_le_mul_of_nonneg_left hm hB).trans small
  have hb' : B*‖λ w‖^2≤(1/2:ℝ)*‖λ w‖ := by
    rw [pow_two,←mul_assoc]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have he' : ‖λ w-w‖≤(1/2:ℝ)*‖λ w‖ := by
    calc
      ‖λ w-w‖ = ‖l (λ w)-λ w‖ := by rw [he,norm_sub_rev]
      _ ≤ B*‖λ w‖^2 := ha
      _ ≤ _ := hb'
  have hs : ‖λ w‖≤(1/2:ℝ)*‖λ w‖+‖w‖ := by
    calc
      _ = ‖(λ w-w)+w‖ := by rw [sub_add_cancel]
      _ ≤ ‖λ w-w‖+‖w‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right he' _
  linarith

include hB small direct read in
/-- The local inverse keeps the old first-order tangent basis. The
constant changes by four because the inverse norm grows by at most
two, not because of any separate rescaling of the Hodge coordinate. -/
theorem inverse_displacement (w : V) (hw : ‖w‖≤ρ/2) :
    ‖λ w-w‖≤(4*B)*‖w‖^2 := by
  have readw := read w hw
  calc
    ‖λ w-w‖ = ‖l (λ w)-λ w‖ := by rw [readw.2,norm_sub_rev]
    _ ≤ B*‖λ w‖^2 := direct _ readw.1
    _ ≤ B*(2*‖w‖)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (inverse_norm l λ hB small direct read w hw) _) hB
    _ = _ := by ring

variable (m : V→V→V) {r C : ℝ}
variable (hρr : ρ≤r/4) (hC : 0≤C) (Csmall : C*r≤1/3)
variable (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2)
variable (addLaw : ∀ x y, ‖x‖≤r/4 → ‖y‖≤r/4 → l (m x y)=l x+l y)
variable (unique : ∀ w z, ‖w‖≤ρ/2 → ‖z‖≤ρ → l z=w → z=λ w)

include hρ hB small direct read hρr hC Csmall quad addLaw unique in
/-- One fixed radius in additive coordinates works for both inputs
and their actual product. It is not a new denominator neighborhood
or an implicit hypothesis that the entire product ball is closed. -/
theorem inverse_local_add (u v : V) (hu : ‖u‖≤ρ/8) (hv : ‖v‖≤ρ/8) :
    m (λ u) (λ v)=λ (u+v) := by
  have up : ‖u‖≤ρ/2 := hu.trans (by linarith)
  have vp : ‖v‖≤ρ/2 := hv.trans (by linarith)
  have sum : ‖u+v‖≤ρ/2 := (norm_add_le u v).trans ((add_le_add hu hv).trans (by linarith))
  have a : ‖λ u‖≤ρ/4 := (inverse_norm l λ hB small direct read u up).trans (by linarith)
  have b : ‖λ v‖≤ρ/4 := (inverse_norm l λ hB small direct read v vp).trans (by linarith)
  have th : ρ/4≤r/4 := by linarith
  have ar := a.trans th
  have br := b.trans th
  have hmax : max ‖λ u‖ ‖λ v‖≤ρ/4 := max_le a b
  have hmax0 : 0≤max ‖λ u‖ ‖λ v‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hcr : C*ρ≤1/3 := (mul_le_mul_of_nonneg_left (by linarith : ρ≤r) hC).trans Csmall
  have hsq : C*(ρ/4)^2≤ρ/48 := by
    calc
      _ = (C*ρ)*(ρ/16) := by ring
      _ ≤ (1/3:ℝ)*(ρ/16) := mul_le_mul_of_nonneg_right hcr (by linarith)
      _ = _ := by ring
  have fits : ‖m (λ u) (λ v)‖≤ρ := by
    have ha := quad (λ u) (λ v) (ar.trans (by linarith)) (br.trans (by linarith))
    have he : ‖m (λ u) (λ v)-(λ u+λ v)‖≤ρ/48 :=
      (ha.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmax0 hmax _) hC)).trans hsq
    calc
      _ = ‖(m (λ u) (λ v)-(λ u+λ v))+(λ u+λ v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖m (λ u) (λ v)-(λ u+λ v)‖+‖λ u+λ v‖ := norm_add_le _ _
      _ ≤ ρ/48+(ρ/4+ρ/4) := add_le_add he ((norm_add_le _ _).trans (add_le_add a b))
      _ ≤ ρ := by linarith
  exact unique _ _ sum fits (by rw [addLaw _ _ ar br,(read u up).2,(read v vp).2])

end ExactInverse

section ComplexRays

variable [NormedSpace ℂ V]
variable (λ : V→V) {ρ B : ℝ} (hρ : 0<ρ)
variable (error : ∀ w, ‖w‖≤ρ/2 → ‖λ w-w‖≤(4*B)*‖w‖^2)

include hρ error in
/-- The original local group path in any complex direction has the
same first-order affine read. Use this error quotient instead of
a new global analytic tangent type; it includes t=0 harmlessly. -/
theorem same_ray_tangent (v : V) :
    Tendsto (fun t : ℂ => t⁻¹ • (λ (t•v)-t•v)) (𝓝 0) (𝓝 0) := by
  have pos : 0<ρ/(2*(‖v‖+1)) := div_pos hρ (by linarith [norm_nonneg v])
  have eventuallySmall : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖<ρ/(2*(‖v‖+1)) :=
    Metric.eventually_nhds_iff.2 ⟨_,pos,fun t ht => by simpa only [dist_zero_right] using ht⟩
  have evBound : ∀ᶠ t : ℂ in 𝓝 0,
      ‖t⁻¹ • (λ (t•v)-t•v)‖≤(4*B)*‖v‖^2*‖t‖ := eventuallySmall.mono (fun t ht => by
    have hg : ‖t‖*(2*(‖v‖+1))≤ρ :=
      (le_div_iff₀ (by linarith [norm_nonneg v] : 0<2*(‖v‖+1))).1 ht.le
    have htNorm : ‖t•v‖≤ρ/2 := by
      rw [norm_smul]
      nlinarith only [hg,norm_nonneg t]
    by_cases z : t=0
    · simp [z]
    · have nn : 0<‖t‖ := norm_pos_iff.2 z
      rw [norm_smul,norm_inv]
      calc
        _ ≤ ‖t‖⁻¹*((4*B)*‖t•v‖^2) :=
          mul_le_mul_of_nonneg_left (error _ htNorm) (inv_nonneg.2 nn.le)
        _ = _ := by
          rw [norm_smul,mul_pow,pow_two ‖t‖]
          calc
            _ = (‖t‖⁻¹*‖t‖)*((4*B)*‖v‖^2*‖t‖) := by ring
            _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt nn),one_mul])
  apply squeeze_zero_norm' evBound
  have h := (continuous_norm.continuousAt (x:=(0:ℂ))).tendsto.const_mul ((4*B)*‖v‖^2)
  simpa only [norm_zero,mul_zero] using h

end ComplexRays

section ActualProducer

variable [NormedSpace ℝ V] [NormedSpace ℂ V]
variable (m : V→V→V) {r C : ℝ}

local notation "Tc" => Spec (CommRingCat.of ℂ)
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : Tc ⟶ E)
variable [MonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]
variable [IsCommMonObj (OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33))]
variable (pt : V→Point a P33 σ) {chart : ℝ}

theorem inverse_source_radius {r₀ C B : ℝ} (start : 0<r₀) (hC : 0≤C) (hB : 0≤B) :
    ∃ r : ℝ, 0<r ∧ r≤r₀ ∧ C*r≤1/3 ∧ B*r≤1/2 := by
  let r := min r₀ (min ((1/3:ℝ)/(C+1)) ((1/2:ℝ)/(B+1)))
  have Cpos : 0<C+1 := by linarith
  have Bpos : 0<B+1 := by linarith
  have pos : 0<r := lt_min start (lt_min (div_pos (by norm_num) Cpos) (div_pos (by norm_num) Bpos))
  have cR : r≤(1/3:ℝ)/(C+1) := (min_le_right _ _).trans (min_le_left _ _)
  have bR : r≤(1/2:ℝ)/(B+1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,pos,min_le_left _ _,?_,?_⟩
  · have e := (le_div_iff₀ Cpos).1 cR
    nlinarith only [e,pos.le]
  · have e := (le_div_iff₀ Bpos).1 bR
    nlinarith only [e,pos.le]

/-- Genuine local inverse of the original installed multiplication in the
same two affine symbols, together with its exact ray tangent. This is
the inverse of the R155 log, not a separate analytic parametrization. -/
theorem actual_inverse_on_marked_points_with_region [CompleteSpace V]
    (rpos : 0<r) (hC : 0≤C) (Csmall : C*r≤1/3)
    (Bsmall : ((2*halfErrorConstant C)/(1-gain))*r≤1/2)
    (origin : pt 0=1) (zero : m 0 0=0)
    (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
    (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
    (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (l λ : V→V), 0<ρ ∧ ρ≤r/4 ∧ l 0=0 ∧ λ 0=0 ∧ pt (λ 0)=1 ∧
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ u v, ‖u‖≤ρ/8 → ‖v‖≤ρ/8 → pt (λ (u+v))=pt (λ u)*pt (λ v)) ∧
      (∀ v, Tendsto (fun t : ℂ => t⁻¹ • (λ (t•v)-t•v)) (𝓝 0) (𝓝 0)) ∧
      (∀ x y, ‖x‖≤ρ → ‖y‖≤ρ → ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖) := by
  obtain ⟨ρ,l,λ,hρ,hρr,l0,ld,ladd,lread,luniq,ηlip⟩ :=
    exists_original_local_log_with_region m a P33 σ pt fit inj law rpos hC Csmall zero defectLip quad
  let B := (2*halfErrorConstant C)/(1-gain)
  have hB : 0≤B := div_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg _))) (sub_pos.2 gain_lt_one).le
  have hρr' : ρ≤r := hρr.trans (by linarith)
  have Bρ : B*ρ≤1/2 := (mul_le_mul_of_nonneg_left hρr' hB).trans Bsmall
  have d (z : V) (hz : ‖z‖≤ρ) : ‖l z-z‖≤B*‖z‖^2 := by
    calc
      _ ≤ (2*halfErrorConstant C)*‖z‖^2/(1-gain) := ld z (hz.trans hρr')
      _ = _ := by unfold B; ring
  have z₀ : ‖(0:V)‖≤ρ := by simpa only [norm_zero] using hρ.le
  have λ0 : λ 0=0 := (luniq 0 0 (by rw [norm_zero]; linarith) z₀ l0).symm
  refine ⟨ρ,l,λ,hρ,hρr,l0,λ0,by rw [λ0,origin],lread,?_,?_,ηlip⟩
  · intro u v hu hv
    have e := inverse_local_add l λ hρ hB Bρ d lread m hρr hC Csmall quad ladd luniq u v hu hv
    have uok : ‖u‖≤ρ/2 := hu.trans (by linarith)
    have vok : ‖v‖≤ρ/2 := hv.trans (by linarith)
    rw [←e]
    exact law _ _ ((lread u uok).1.trans hρr') ((lread v vok).1.trans hρr')
  · exact same_ray_tangent λ hρ (inverse_displacement l λ hB Bρ d lread)

theorem actual_inverse_on_marked_points [CompleteSpace V]
    (rpos : 0<r) (hC : 0≤C) (Csmall : C*r≤1/3)
    (Bsmall : ((2*halfErrorConstant C)/(1-gain))*r≤1/2)
    (origin : pt 0=1) (zero : m 0 0=0)
    (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
    (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
    (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (l λ : V→V), 0<ρ ∧ ρ≤r/4 ∧ l 0=0 ∧ λ 0=0 ∧ pt (λ 0)=1 ∧
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ u v, ‖u‖≤ρ/8 → ‖v‖≤ρ/8 → pt (λ (u+v))=pt (λ u)*pt (λ v)) ∧
      (∀ v, Tendsto (fun t : ℂ => t⁻¹ • (λ (t•v)-t•v)) (𝓝 0) (𝓝 0)) := by
  obtain ⟨ρ,l,λ,rp,rr,l0,λ0,pt0,read,add,rays,_⟩ :=
    actual_inverse_on_marked_points_with_region m a P33 σ pt rpos hC Csmall Bsmall
      origin zero fit inj law defectLip quad
  exact ⟨ρ,l,λ,rp,rr,l0,λ0,pt0,read,add,rays⟩

end ActualProducer

end OriginalRetainedDyadicInverseRay318
