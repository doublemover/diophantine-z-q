module
public import BoundedRectanglePrimitiveClosure318
public import VanishingDerivativeTrace318
public import Mathlib.Analysis.Complex.RealDeriv
public section
noncomputable section
namespace ActualBoundedPrimitiveTraces318
open Set Metric Filter
open scoped Topology ComplexConjugate
open HolomorphicRectanglePrimitive318 BoundedRectanglePrimitiveClosure318
set_option maxHeartbeats 2800000

/-- Put the actual uniformly extended primitive on the ambient plane.
Its values off the closure are immaterial; its derivative on the original
open rectangle and continuity on the whole closure are constructed. -/
theorem ambient_bounded_primitive (f : ℂ → ℂ) {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hne : (openRectangle a b c d).Nonempty) (C : NNReal)
    (hC : ∀z∈openRectangle a b c d,‖f z‖₊≤C) :
    ∃g:ℂ→ℂ,ContinuousOn g (closure (openRectangle a b c d)) ∧
      ∀z∈openRectangle a b c d,HasDerivAt g (f z) z := by
  classical
  obtain ⟨p,P,hp,_,hPu,hPe⟩ := bounded_holomorphic_primitive_closure f hf hne C hC
  let U := openRectangle a b c d
  let g : ℂ→ℂ := fun z=>if hz:z∈closure U then P ⟨z,hz⟩ else 0
  have heq : ∀z∈U,g z=p z := by
    intro z hz
    simp only [g,dif_pos (subset_closure hz)]
    exact hPe ⟨z,hz⟩
  refine ⟨g,?_,?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous ((closure U).domRestrict g)
    have he : (closure U).domRestrict g=P := by
      funext z
      change (if hz:(z:ℂ)∈closure U then P ⟨z,hz⟩ else 0)=P z
      rw [dif_pos z.property]
      exact congrArg P (Subtype.ext rfl)
    rw [he]
    exact hPu.continuous
  · intro z hz
    apply (hp z hz).congr_of_eventuallyEq
    filter_upwards [(openRectangle_open a b c d).mem_nhds hz] with w hw
    exact heq w hw

/-- Continuity of the CONSTRUCTED primitive on its actual closure gives
all approaching trace limits. The boundary point belongs to that closure
because the approaching path is eventually inside, not by assumption. -/
theorem closure_trace_limit {T : Type*} (l : Filter T) [NeBot l]
    (U : Set ℂ) (g : ℂ→ℂ) (hg : ContinuousOn g (closure U))
    (path : T→ℂ) (x:ℂ) (hx : Tendsto path l (𝓝 x))
    (hp : ∀ᶠt in l,path t∈U) : Tendsto (fun t=>g (path t)) l (𝓝 (g x)) := by
  have hxU : x∈closure U := mem_closure_of_tendsto hx hp
  apply (hg x hxU).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hx,hp.mono (fun _ h=>subset_closure h)⟩

@[expose] def upperPath (x t:ℝ) : ℂ := (x:ℂ)+Complex.I*t
@[expose] def lowerPath (x t:ℝ) : ℂ := (x:ℂ)-Complex.I*t

theorem upper_path_limit (x:ℝ) :
    Tendsto (upperPath x) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
  have hc : Continuous (upperPath x) := by unfold upperPath; fun_prop
  simpa only [upperPath,Complex.ofReal_zero,mul_zero,add_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

theorem lower_path_limit (x:ℝ) :
    Tendsto (lowerPath x) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
  have hc : Continuous (lowerPath x) := by unfold lowerPath; fun_prop
  simpa only [lowerPath,Complex.ofReal_zero,mul_zero,sub_zero] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

theorem upper_path_mem {a b r x t:ℝ} (hx:x∈Ioo a b) (ht:0<t) (htr:t<r) :
    upperPath x t∈openRectangle a b 0 r := by
  change (upperPath x t).re∈Ioo a b ∧ (upperPath x t).im∈Ioo 0 r
  simpa [upperPath] using And.intro hx (And.intro ht htr)

theorem lower_path_mem {a b r x t:ℝ} (hx:x∈Ioo a b) (ht:0<t) (htr:t<r) :
    lowerPath x t∈openRectangle a b (-r) 0 := by
  change (lowerPath x t).re∈Ioo a b ∧ (lowerPath x t).im∈Ioo (-r) 0
  have hi : -t∈Ioo (-r) 0 := ⟨neg_lt_neg htr,neg_lt_zero.mpr ht⟩
  simpa [lowerPath] using And.intro hx hi

theorem upper_horizontal_derivative (g:ℂ→ℂ) (v:ℂ) (x t:ℝ)
    (hg:HasDerivAt g v (upperPath x t)) :
    HasDerivAt (fun y:ℝ=>g (upperPath y t)) v x := by
  have hh := hg.comp (x:ℂ) ((hasDerivAt_id (x:ℂ)).add_const (Complex.I*t))
  simpa [upperPath] using hh.comp_ofReal

theorem lower_horizontal_derivative (g:ℂ→ℂ) (v:ℂ) (x t:ℝ)
    (hg:HasDerivAt g v (lowerPath x t)) :
    HasDerivAt (fun y:ℝ=>g (lowerPath y t)) v x := by
  have hh := hg.comp (x:ℂ) ((hasDerivAt_id (x:ℂ)).sub_const (Complex.I*t))
  simpa [lowerPath] using hh.comp_ofReal

/-- On every compact subsegment, the actual upper/lower primitive
traces differ by the same constant. All horizontal derivatives and trace
limits are derived from the original complex primitives. -/
theorem matching_on_segment (f_plus f_minus g_plus g_minus:ℂ→ℂ) {a b r u v:ℝ}
    (hr:0<r) (hau:a<u) (huv:u≤v) (hvb:v<b)
    (hc_plus:ContinuousOn g_plus (closure (openRectangle a b 0 r)))
    (hc_minus:ContinuousOn g_minus (closure (openRectangle a b (-r) 0)))
    (hd_plus:∀z∈openRectangle a b 0 r,HasDerivAt g_plus (f_plus z) z)
    (hd_minus:∀z∈openRectangle a b (-r) 0,HasDerivAt g_minus (f_minus z) z)
    (hjump:∀x∈Icc u v,Tendsto (fun z=>f_plus z-f_minus (conj z))
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 0)) :
    ∀x∈Icc u v,g_plus (x:ℂ)-g_minus (x:ℂ)=g_plus (u:ℂ)-g_minus (u:ℂ) := by
  have hinside : ∀x∈Icc u v,x∈Ioo a b := fun x hx=>
    ⟨hau.trans_le hx.1,hx.2.trans_lt hvb⟩
  have htr : ∀ᶠt in 𝓝[>] (0:ℝ),t<r := nhdsWithin_le_nhds (eventually_lt_nhds hr)
  have hp_plus (x:ℝ) (hx:x∈Icc u v) :
      ∀ᶠt in 𝓝[>] (0:ℝ),upperPath x t∈openRectangle a b 0 r := by
    filter_upwards [self_mem_nhdsWithin,htr] with t ht hrt
    exact upper_path_mem (hinside x hx) ht hrt
  have hp_minus (x:ℝ) (hx:x∈Icc u v) :
      ∀ᶠt in 𝓝[>] (0:ℝ),lowerPath x t∈openRectangle a b (-r) 0 := by
    filter_upwards [self_mem_nhdsWithin,htr] with t ht hrt
    exact lower_path_mem (hinside x hx) ht hrt
  let F : ℝ→ℝ→ℂ := fun t x=>g_plus (upperPath x t)-g_minus (lowerPath x t)
  let D : ℝ→ℝ→ℂ := fun t x=>f_plus (upperPath x t)-f_minus (lowerPath x t)
  apply VanishingDerivativeTrace318.limit_constant_of_uniform_derivative
    (𝓝[>] (0:ℝ)) F D (fun x=>g_plus (x:ℂ)-g_minus (x:ℂ)) huv
  · intro x hx
    exact (closure_trace_limit _ _ g_plus hc_plus _ _ (upper_path_limit x) (hp_plus x hx)).sub
      (closure_trace_limit _ _ g_minus hc_minus _ _ (lower_path_limit x) (hp_minus x hx))
  · intro ε hε
    let K:Set ℂ := Complex.ofReal '' Icc u v
    obtain ⟨δ,hδ,hbound⟩ := CompactBoundaryJump318.uniform_zero_near_compact
      (openRectangle a b 0 r) K (isCompact_Icc.image Complex.continuous_ofReal)
      (fun z=>f_plus z-f_minus (conj z)) (by rintro z ⟨x,hx,rfl⟩;exact hjump x hx) hε
    have htδ : ∀ᶠt in 𝓝[>] (0:ℝ),t<δ := nhdsWithin_le_nhds (eventually_lt_nhds hδ)
    filter_upwards [self_mem_nhdsWithin,htr,htδ] with t ht hrt hdt
    intro x hx
    have hx_plus := upper_path_mem (hinside x hx) ht hrt
    have hx_minus := lower_path_mem (hinside x hx) ht hrt
    refine ⟨((upper_horizontal_derivative g_plus _ x t (hd_plus _ hx_plus)).sub
      (lower_horizontal_derivative g_minus _ x t (hd_minus _ hx_minus))).hasDerivWithinAt,?_⟩
    have hnear : upperPath x t∈thickening δ K := by
      apply mem_thickening_iff.mpr
      refine ⟨(x:ℂ),⟨x,hx,rfl⟩,?_⟩
      simpa [upperPath,dist_eq_norm,norm_mul,Complex.norm_real,abs_of_pos ht] using hdt
    have he : conj (upperPath x t)=lowerPath x t := by simp [upperPath,lowerPath]
    have hb := (hbound _ hnear hx_plus).le
    simpa only [D,he] using hb
/-- The one constant works on the WHOLE open seam, not merely on a
chosen compact sample. Every point is compared with the same midpoint. -/
theorem matching_on_open_seam (f_plus f_minus g_plus g_minus:ℂ→ℂ) {a b r:ℝ}
    (hab:a<b) (hr:0<r)
    (hc_plus:ContinuousOn g_plus (closure (openRectangle a b 0 r)))
    (hc_minus:ContinuousOn g_minus (closure (openRectangle a b (-r) 0)))
    (hd_plus:∀z∈openRectangle a b 0 r,HasDerivAt g_plus (f_plus z) z)
    (hd_minus:∀z∈openRectangle a b (-r) 0,HasDerivAt g_minus (f_minus z) z)
    (hjump:∀x∈Ioo a b,Tendsto (fun z=>f_plus z-f_minus (conj z))
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 0)) :
    ∃c:ℂ,∀x∈Ioo a b,g_plus (x:ℂ)=g_minus (x:ℂ)+c := by
  let m:ℝ := (a+b)/2
  have hm:m∈Ioo a b := by dsimp [m];constructor <;> linarith
  refine ⟨g_plus (m:ℂ)-g_minus (m:ℂ),?_⟩
  intro x hx
  have hu:a<min x m := lt_min hx.1 hm.1
  have hv:max x m<b := max_lt hx.2 hm.2
  have hh := matching_on_segment f_plus f_minus g_plus g_minus hr hu (min_le_max) hv hc_plus hc_minus hd_plus hd_minus
    (fun y hy=>hjump y ⟨hu.trans_le hy.1,hy.2.trans_lt hv⟩)
  have h₁ := hh x ⟨min_le_left _ _,le_max_left _ _⟩
  have h₂ := hh m ⟨min_le_right _ _,le_max_right _ _⟩
  linear_combination h₁-h₂

/-- Starting only from two bounded holomorphic functions and their
vanishing actual boundary jump, construct both primitives, their genuine
closure values, and the additive matching constant. -/
theorem bounded_pair_matching_primitives (f_plus f_minus:ℂ→ℂ) {a b r:ℝ}
    (hab:a<b) (hr:0<r)
    (hf_plus:DifferentiableOn ℂ f_plus (openRectangle a b 0 r))
    (hf_minus:DifferentiableOn ℂ f_minus (openRectangle a b (-r) 0))
    (C_plus C_minus:NNReal)
    (hC_plus:∀z∈openRectangle a b 0 r,‖f_plus z‖₊≤C_plus)
    (hC_minus:∀z∈openRectangle a b (-r) 0,‖f_minus z‖₊≤C_minus)
    (hjump:∀x∈Ioo a b,Tendsto (fun z=>f_plus z-f_minus (conj z))
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 0)) :
    ∃g_plus g_minus:ℂ→ℂ,∃c:ℂ,
      ContinuousOn g_plus (closure (openRectangle a b 0 r)) ∧
      ContinuousOn g_minus (closure (openRectangle a b (-r) 0)) ∧
      (∀z∈openRectangle a b 0 r,HasDerivAt g_plus (f_plus z) z) ∧
      (∀z∈openRectangle a b (-r) 0,HasDerivAt g_minus (f_minus z) z) ∧
      (∀x∈Ioo a b,g_plus (x:ℂ)=g_minus (x:ℂ)+c) := by
  have hm:(a+b)/2∈Ioo a b := by constructor <;> linarith
  have ht:0<r/2 := by linarith
  have htr:r/2<r := by linarith
  obtain ⟨g_plus,hc_plus,hd_plus⟩ := ambient_bounded_primitive f_plus hf_plus
    ⟨upperPath ((a+b)/2) (r/2),upper_path_mem hm ht htr⟩ C_plus hC_plus
  obtain ⟨g_minus,hc_minus,hd_minus⟩ := ambient_bounded_primitive f_minus hf_minus
    ⟨lowerPath ((a+b)/2) (r/2),lower_path_mem hm ht htr⟩ C_minus hC_minus
  obtain ⟨c,hc⟩ := matching_on_open_seam f_plus f_minus g_plus g_minus hab hr hc_plus hc_minus hd_plus hd_minus hjump
  exact ⟨g_plus,g_minus,c,hc_plus,hc_minus,hd_plus,hd_minus,hc⟩
end ActualBoundedPrimitiveTraces318
