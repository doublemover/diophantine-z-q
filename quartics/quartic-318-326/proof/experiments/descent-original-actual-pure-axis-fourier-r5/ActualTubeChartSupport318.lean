module
public import ActualTubeAnnulusChart318
import all ActualTubeAnnulusChart318
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public section
noncomputable section
namespace ActualTubeChartSupport318
open ActualTubeAnnulusChart318
open scoped ContDiff Topology SchwartzMap

private theorem χ_smooth : ContDiff ℝ ∞ χ := annulusBump.contDiff
private theorem ζ_smooth : ContDiff ℝ ∞ ζ := shiftBump.contDiff
private theorem off_smooth : ContDiff ℝ ∞ off := contDiff_const.sub chartBump.contDiff

/-- Uses the outer cutoff, not the unit-height region of the shift bump. -/
theorem ζ_zero (u : ℝ) (hu : 2≤ |u|) : ζ u=0 := by
  apply shiftBump.zero_of_le_dist
  rw [Real.dist_eq,sub_zero]
  exact hu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem selector_comp_smoothAt {x y z t : E→ℝ} {p : E} (i : Fin 4)
    (hx : ContDiffAt ℝ ∞ x p) (hy : ContDiffAt ℝ ∞ y p)
    (hz : ContDiffAt ℝ ∞ z p) (ht : ContDiffAt ℝ ∞ t p) :
    ContDiffAt ℝ ∞ (fun u => selector i (x u) (y u) (z u) (t u)) p := by
  have Hx : ContDiffAt ℝ ∞ (fun u => off (x u)) p :=
    off_smooth.comp_contDiffAt p hx
  have Hy : ContDiffAt ℝ ∞ (fun u => off (y u)) p :=
    off_smooth.comp_contDiffAt p hy
  have Hz : ContDiffAt ℝ ∞ (fun u => off (z u)) p :=
    off_smooth.comp_contDiffAt p hz
  have Ht : ContDiffAt ℝ ∞ (fun u => off (t u)) p :=
    off_smooth.comp_contDiffAt p ht
  have Hx' : ContDiffAt ℝ ∞ (fun u => 1-off (x u)) p := contDiffAt_const.sub Hx
  have Hy' : ContDiffAt ℝ ∞ (fun u => 1-off (y u)) p := contDiffAt_const.sub Hy
  have Hz' : ContDiffAt ℝ ∞ (fun u => 1-off (z u)) p := contDiffAt_const.sub Hz
  fin_cases i
  · simpa [selector] using Hx
  · simpa [selector] using Hx'.mul Hy
  · simpa [selector] using (Hx'.mul Hy').mul Hz
  · simpa [selector] using ((Hx'.mul Hy').mul Hz').mul Ht

private theorem hyper_weight_comp_smoothAt {x y z t v : E→ℝ} {p : E}
    (τ : ℝ) (i : Fin 4)
    (hx : ContDiffAt ℝ ∞ x p) (hy : ContDiffAt ℝ ∞ y p)
    (hz : ContDiffAt ℝ ∞ z p) (ht : ContDiffAt ℝ ∞ t p)
    (hv : ContDiffAt ℝ ∞ v p) :
    ContDiffAt ℝ ∞ (fun u => tube τ ((x u+y u)/2) ((z u+t u)/2)
      ((y u-x u)/2) ((t u-z u)/2) (v u) * selector i (x u) (y u) (z u) (t u)) p := by
  have ha := (hx.add hy).div_const 2
  have hb := (hz.add ht).div_const 2
  have hc := (hy.sub hx).div_const 2
  have hd := (ht.sub hz).div_const 2
  have h₁ := χ_smooth.comp_contDiffAt p ((ha.pow 2).add (hb.pow 2))
  have h₂ := χ_smooth.comp_contDiffAt p ((hc.pow 2).add (hd.pow 2))
  have h₃ := ζ_smooth.comp_contDiffAt p (hv.div_const τ)
  simpa only [tube, Function.comp_apply] using
    ((h₁.mul h₂).mul h₃).mul (selector_comp_smoothAt i hx hy hz ht)

/-- This is the only branch which differentiates a variable denominator. -/
theorem section_comp_contDiffAt_nonzero {x z t v : E→ℝ} {p : E}
    (κ τ : ℝ) (i : Fin 4)
    (hx : ContDiffAt ℝ ∞ x p) (hz : ContDiffAt ℝ ∞ z p)
    (ht : ContDiffAt ℝ ∞ t p) (hv : ContDiffAt ℝ ∞ v p) (h₀ : x p≠0) :
    ContDiffAt ℝ ∞ (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) p := by
  have hY : ContDiffAt ℝ ∞ (fun u => eliminated κ (x u) (z u) (t u) (v u)) p := by
    have hnum : ContDiffAt ℝ ∞ (fun u => κ*(v u)^2-z u*t u) p :=
      (contDiffAt_const.mul (hv.pow 2)).sub (hz.mul ht)
    simpa only [eliminated] using hnum.fun_div hx h₀
  fin_cases i
  · simpa [sectionWeight,undo] using hyper_weight_comp_smoothAt τ 0 hx hY hz ht hv
  · simpa [sectionWeight,undo] using hyper_weight_comp_smoothAt τ 1 hY hx hz ht hv
  · simpa [sectionWeight,undo] using hyper_weight_comp_smoothAt τ 2 hz ht hx hY hv
  · simpa [sectionWeight,undo] using hyper_weight_comp_smoothAt τ 3 hz ht hY hx hv

/-- Any continuous coordinate map landing strictly inside the flat band
has a genuinely constant-zero germ. This includes the rational seam. -/
theorem section_comp_eventually_zero {x z t v : E→ℝ} {p : E}
    (κ τ : ℝ) (i : Fin 4) (hx : ContinuousAt x p) (h₀ : |x p| <1/8) :
    (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) =ᶠ[𝓝 p] (fun _ => 0) := by
  have h : ∀ᶠ u in 𝓝 p, |x u| <1/8 :=
    hx.abs.eventually (gt_mem_nhds h₀)
  filter_upwards [h] with u hu
  exact section_zero_small κ τ i (x u) (z u) (t u) (v u) hu.le

theorem section_comp_contDiffAt {x z t v : E→ℝ} {p : E}
    (κ τ : ℝ) (i : Fin 4)
    (hx : ContDiffAt ℝ ∞ x p) (hz : ContDiffAt ℝ ∞ z p)
    (ht : ContDiffAt ℝ ∞ t p) (hv : ContDiffAt ℝ ∞ v p) :
    ContDiffAt ℝ ∞ (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) p := by
  by_cases h : x p=0
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0:ℝ)) p).congr_of_eventuallyEq
    apply section_comp_eventually_zero κ τ i hx.continuousAt
    norm_num [h]
  · exact section_comp_contDiffAt_nonzero κ τ i hx hz ht hv h

/-- Applies to a full parameter tuple or any of its coordinate charts/slices. -/
theorem section_comp_contDiff {x z t v : E→ℝ} (κ τ : ℝ) (i : Fin 4)
    (hx : ContDiff ℝ ∞ x) (hz : ContDiff ℝ ∞ z)
    (ht : ContDiff ℝ ∞ t) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) :=
  contDiff_iff_contDiffAt.mpr (fun _ =>
    section_comp_contDiffAt κ τ i hx.contDiffAt hz.contDiffAt ht.contDiffAt hv.contDiffAt)

private theorem abs_le_two_of_norm_lt {a b : ℝ} (h : a^2+b^2<5/4) : |a| ≤2 := by
  by_contra! h'
  have hsq : 4<a^2 := by
    have hp := mul_pos (sub_pos.mpr h') (show 0 < |a| + 2 by positivity)
    have he : |a|^2=a^2 := sq_abs a
    nlinarith only [hp,he]
  nlinarith only [h,hsq,sq_nonneg b]

private theorem abs_le_four_sub {a b : ℝ} (ha : |a| ≤2) (hb : |b| ≤2) : |a-b| ≤4 := by
  simpa only [sub_eq_add_neg,abs_neg] using
    (abs_add_le a (-b)).trans (by rw [abs_neg]; linarith)

private theorem hyper_nonzero_box (τ x y z t v : ℝ) (i : Fin 4) (hτ : 0<τ)
    (hne : tube τ ((x+y)/2) ((z+t)/2) ((y-x)/2) ((t-z)/2) v *
      selector i x y z t≠0) :
    |x| ≤4 ∧ |y| ≤4 ∧ |z| ≤4 ∧ |t| ≤4 ∧ |v| <2*τ := by
  let a := (x+y)/2
  let b := (z+t)/2
  let c := (y-x)/2
  let d := (t-z)/2
  have hn₁ : a^2+b^2<5/4 := by
    by_contra! H
    exact hne (by simp [tube,χ_zero_high _ H,a,b])
  have hn₂ : c^2+d^2<5/4 := by
    by_contra! H
    exact hne (by simp [tube,χ_zero_high _ H,c,d])
  have hv : |v/τ| <2 := by
    by_contra! H
    exact hne (by simp [tube,ζ_zero _ H])
  have ha := abs_le_two_of_norm_lt hn₁
  have hb := abs_le_two_of_norm_lt (by linarith only [hn₁] : b^2+a^2<5/4)
  have hc := abs_le_two_of_norm_lt hn₂
  have hd := abs_le_two_of_norm_lt (by linarith only [hn₂] : d^2+c^2<5/4)
  have hx : a-c=x := by dsimp [a,c]; ring
  have hy : a+c=y := by dsimp [a,c]; ring
  have hz : b-d=z := by dsimp [b,d]; ring
  have ht : b+d=t := by dsimp [b,d]; ring
  refine ⟨?_,?_,?_,?_,(div_lt_iff₀ hτ).mp (by simpa only [abs_div,abs_of_pos hτ] using hv)⟩
  · rw [←hx]; exact abs_le_four_sub ha hc
  · rw [←hy]; exact (abs_add_le a c).trans (by linarith)
  · rw [←hz]; exact abs_le_four_sub hb hd
  · rw [←ht]; exact (abs_add_le b d).trans (by linarith)

/-- Closed support in all affine directions; strict top bound on V is
stronger at nonzero points. No denominator estimate is needed here. -/
theorem section_nonzero_box (κ τ : ℝ) (i : Fin 4) (X Z T V : ℝ) (hτ : 0<τ)
    (hne : sectionWeight κ τ i X Z T V≠0) :
    1/8< |X| ∧ |X| ≤4 ∧ |Z| ≤4 ∧ |T| ≤4 ∧ |V| <2*τ := by
  have hl : 1/8< |X| := by
    by_contra! H
    exact hne (section_zero_small κ τ i X Z T V H)
  let p := undo i X (eliminated κ X Z T V) Z T
  have Hb := hyper_nonzero_box τ p.1 p.2.1 p.2.2.1 p.2.2.2 V i hτ hne
  refine ⟨hl,?_⟩
  dsimp [p] at Hb
  fin_cases i <;> simp [undo] at Hb <;> tauto

theorem section_zero_Z {κ τ X Z T V : ℝ} {i : Fin 4} (hτ : 0<τ) (h : 4< |Z|) :
    sectionWeight κ τ i X Z T V=0 := by
  by_contra hn
  exact (not_lt_of_ge (section_nonzero_box κ τ i X Z T V hτ hn).2.2.1) h

theorem section_zero_T {κ τ X Z T V : ℝ} {i : Fin 4} (hτ : 0<τ) (h : 4< |T|) :
    sectionWeight κ τ i X Z T V=0 := by
  by_contra hn
  exact (not_lt_of_ge (section_nonzero_box κ τ i X Z T V hτ hn).2.2.2.1) h

theorem section_zero_V {κ τ X Z T V : ℝ} {i : Fin 4} (hτ : 0<τ) (h : 2*τ≤ |V|) :
    sectionWeight κ τ i X Z T V=0 := by
  by_contra hn
  exact (not_lt_of_ge h) (section_nonzero_box κ τ i X Z T V hτ hn).2.2.2.2

/-- Open exterior splices for the actual mixed-jet producer. No claim of
a constant germ at V=±2τ is required for closed-box support. -/
theorem section_comp_eventually_zero_T {x z t v : E→ℝ} {p : E}
    (κ τ : ℝ) (i : Fin 4) (hτ : 0<τ) (ht : ContinuousAt t p) (h₀ : 4< |t p|) :
    (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) =ᶠ[𝓝 p] (fun _ => 0) := by
  have h : ∀ᶠ u in 𝓝 p, 4< |t u| := ht.abs.eventually (lt_mem_nhds h₀)
  filter_upwards [h] with u hu
  exact section_zero_T hτ hu

theorem section_comp_eventually_zero_V {x z t v : E→ℝ} {p : E}
    (κ τ : ℝ) (i : Fin 4) (hτ : 0<τ) (hv : ContinuousAt v p) (h₀ : 2*τ< |v p|) :
    (fun u => sectionWeight κ τ i (x u) (z u) (t u) (v u)) =ᶠ[𝓝 p] (fun _ => 0) := by
  have h : ∀ᶠ u in 𝓝 p, 2*τ< |v u| := hv.abs.eventually (lt_mem_nhds h₀)
  filter_upwards [h] with u hu
  exact section_zero_V hτ hu.le

/-- Locality alone handles every scalar derivative on the exterior.
No induction on, or bounds for, the rational chart jets occur here. -/
theorem iteratedDeriv_zero_of_zero_germ {f : ℝ→ℂ} {s : ℝ}
    (h : f =ᶠ[𝓝 s] (fun _ => 0)) (n : ℕ) : iteratedDeriv n f s=0 := by
  rw [h.iteratedDeriv_eq n]
  cases n <;> simp [iteratedDeriv_const]

theorem support_Y (κ τ : ℝ) (i : Fin 4) (X Z T V : ℝ)
    (hτ : 0<τ) (h : 4< |T|) (n : ℕ) :
    iteratedDeriv n (fun u => (sectionWeight κ τ i X Z u V:ℂ)) T=0 := by
  apply iteratedDeriv_zero_of_zero_germ _ n
  have h₀ : (fun u => sectionWeight κ τ i X Z u V) =ᶠ[𝓝 T] (fun _ => 0) :=
    section_comp_eventually_zero_T κ τ i hτ continuousAt_id h
  filter_upwards [h₀] with u hu
  change (sectionWeight κ τ i X Z u V:ℂ)=0
  simp [show sectionWeight κ τ i X Z u V = 0 from hu]

theorem support_Z (κ τ : ℝ) (i : Fin 4) (X Z T V : ℝ)
    (hτ : 0<τ) (h : 2*τ< |V|) (n : ℕ) :
    iteratedDeriv n (fun u => (sectionWeight κ τ i X Z T u:ℂ)) V=0 := by
  apply iteratedDeriv_zero_of_zero_germ _ n
  have h₀ : (fun u => sectionWeight κ τ i X Z T u) =ᶠ[𝓝 V] (fun _ => 0) :=
    section_comp_eventually_zero_V κ τ i hτ continuousAt_id h
  filter_upwards [h₀] with u hu
  change (sectionWeight κ τ i X Z T u:ℂ)=0
  simp [show sectionWeight κ τ i X Z T u = 0 from hu]

/-- At a fixed empty X chart all affine variables may vary arbitrarily.
In particular this gives the zero jet also at |X|=1/8; it does not
assert vanishing of an X derivative by an open neighborhood there. -/
theorem fixed_empty {κ τ X : ℝ} {i : Fin 4} (hX : |X| ≤1/8) :
    (fun p : ℝ×ℝ×ℝ => (sectionWeight κ τ i X p.1 p.2.1 p.2.2:ℂ))=0 := by
  funext p
  simp [section_zero_small κ τ i X p.1 p.2.1 p.2.2 hX]

theorem affine_smooth (κ τ : ℝ) (i : Fin 4) (X : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ×ℝ×ℝ => (sectionWeight κ τ i X p.1 p.2.1 p.2.2:ℂ)) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ×ℝ×ℝ => sectionWeight κ τ i X p.1 p.2.1 p.2.2) :=
    section_comp_contDiff κ τ i contDiff_const contDiff_fst
      (contDiff_fst.comp contDiff_snd) (contDiff_snd.comp contDiff_snd)
  exact Complex.ofRealCLM.contDiff.comp h

/-- One concrete field of the Poisson input is now available without any
derivative estimate: the first-coordinate Schwartz row itself. -/
def xrow (κ τ : ℝ) (i : Fin 4) (X T V : ℝ) (hτ : 0<τ) : 𝓢(ℝ,ℂ) := by
  let f : ℝ→ℂ := fun z => (sectionWeight κ τ i X z T V:ℂ)
  have hs : Function.support f ⊆ Set.Icc (-4) 4 := by
    intro z hz
    by_contra hn
    have h : 4< |z| := by
      by_contra! h
      exact hn (by simpa only [Set.mem_Icc,abs_le] using h)
    exact hz (by
      change (sectionWeight κ τ i X z T V:ℂ)=0
      rw [section_zero_Z (κ:=κ) (X:=X) (T:=T) (V:=V) (i:=i) hτ h, Complex.ofReal_zero])
  have hc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_Icc)
  have hd : ContDiff ℝ ∞ (fun z : ℝ => sectionWeight κ τ i X z T V) :=
    section_comp_contDiff κ τ i contDiff_const contDiff_id contDiff_const contDiff_const
  exact hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd)

-- The body of xrow stays non-exposed. Unfold only in this private
-- pointwise proof, then export a propositional equality via funext.
private theorem xrow_apply_internal (κ τ : ℝ) (i : Fin 4) (X T V : ℝ)
    (hτ : 0<τ) (z : ℝ) :
    xrow κ τ i X T V hτ z = (sectionWeight κ τ i X z T V:ℂ) := by
  unfold xrow <;> rfl

theorem xrow_eq (κ τ : ℝ) (i : Fin 4) (X T V : ℝ) (hτ : 0<τ) :
    (xrow κ τ i X T V hτ : ℝ→ℂ)=fun z => (sectionWeight κ τ i X z T V:ℂ) :=
  funext (xrow_apply_internal κ τ i X T V hτ)

end ActualTubeChartSupport318
