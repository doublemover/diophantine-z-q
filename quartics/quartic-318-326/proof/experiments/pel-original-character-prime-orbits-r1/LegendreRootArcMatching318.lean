module
public import LegendreRealStripSheets318
public section
noncomputable section
namespace LegendreRootArcMatching318
open Set Filter
open scoped Topology
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalRealStripCover318 LegendreHalfPlaneAnalyticSheets318
open LegendreRealStripSheets318
abbrev Interior:=Ioo (0:ℝ) 1

/-- Real-parameter version of constant square-root sign, used for entire
crossing arcs. Its domain is the connected original path interior. -/
lemma arc_sign {f g:ℝ→ℂ} (hf:ContinuousOn f Interior) (hg:ContinuousOn g Interior)
    (he:∀t∈Interior,f t^2=g t^2) (hn:∀t∈Interior,g t≠0) :
    ∃s:ℂ,s^2=1 ∧ ∀t∈Interior,f t=s*g t := by
  let r:ℝ→ℂ:=fun t=>f t/g t
  have hr:ContinuousOn r Interior:=hf.div hg hn
  have hs:∀t∈Interior,r t^2=1:=by
    intro t ht
    dsimp [r]
    rw [div_pow,he t ht,div_self (pow_ne_zero 2 (hn t ht))]
  have hm:MapsTo r Interior ({1,-1}:Set ℂ):=by
    intro t ht
    have hh:r t^2=(1:ℂ)^2:=by simpa using hs t ht
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h|h <;> simp [h]
  have hd:IsDiscrete ({1,-1}:Set ℂ):=by
    letI:Fintype ↥({1,-1}:Set ℂ):=((Set.finite_singleton (-1:ℂ)).insert 1).fintype
    rw [isDiscrete_iff_discreteTopology]
    infer_instance
  have hc:IsPreconnected Interior:=(convex_Ioo (0:ℝ) 1).isPreconnected
  have ha:(1/2:ℝ)∈Interior:=by constructor <;> norm_num
  refine ⟨r (1/2),hs _ ha,?_⟩
  intro t ht
  have hconst:r t=r (1/2):=hc.constant_of_mapsTo hd hr hm ht ha
  exact (div_mul_cancel₀ (f t) (hn t ht)).symm.trans (congrArg (fun z=>z*g t) hconst)

variable (i:Fin 4)
/-- The SAME fixed global halfplane root equals one fixed sign times any
actual nonzero continuous square-root lift along the entire base arc. -/
theorem one_root (upper:Bool) (base lift:ℝ→ℂ)
    (hb:ContinuousOn base Interior) (hl:ContinuousOn lift Interior)
    (hs:∀t∈Interior,base t∈domain upper)
    (he:∀t∈Interior,lift t^2=polynomial (branchParameter i) (base t)) :
    ∃s:ℂ,s^2=1 ∧ ∀t∈Interior,
      LegendreHalfPlaneAnalyticSheets318.root (branchParameter i) (branchParameter_im_zero i) upper (base t)=s*lift t := by
  apply arc_sign
  · exact (LegendreHalfPlaneAnalyticSheets318.root_analytic _ _ upper).continuousOn.comp hb hs
  · exact hl
  · intro t ht
    rw [LegendreHalfPlaneAnalyticSheets318.root_square,he t ht]
  · intro t ht hz
    have hh:=he t ht
    rw [hz,zero_pow (by decide : 2≠0)] at hh
    exact polynomial_nonzero _ (branchParameter_im_zero i) upper (base t) (hs t ht) hh.symm

variable {i} (J:Interval i)
@[expose] def seamRoot (upper:Bool) (a:ℝ) : ℂ:=halfSign J upper*stripRoot J (a:ℂ)
lemma seam_transition (a:ℝ) : seamRoot J true a=transitionSign J*seamRoot J false a := by
  dsimp [seamRoot,transitionSign]
  have hs:=halfSign_square J false
  linear_combination -(halfSign J true*stripRoot J (a:ℂ))*hs

/-- Genuine endpoint equality is derived by limits of the same strip
root and actual lifted path, for either approaching endpoint filter. -/
theorem endpoint (upper:Bool) (base lift:ℝ→ℂ) (s:ℂ)
    (hs:∀t∈Interior,base t∈domain upper)
    (he:∀t∈Interior,LegendreHalfPlaneAnalyticSheets318.root
      (branchParameter i) (branchParameter_im_zero i) upper (base t)=s*lift t)
    (t₀ a:ℝ) (ha:a∈J.carrier) (hbase:base t₀=(a:ℂ))
    (hb:ContinuousAt base t₀) (hl:ContinuousAt lift t₀)
    (L:Filter ℝ) [NeBot L] (hL:Tendsto id L (𝓝 t₀))
    (hinter:∀ᶠ t in L,t∈Interior) : seamRoot J upper a=s*lift t₀ := by
  have hm:base t₀∈J.Domain:=by rw [hbase];exact ha
  have ht:Tendsto base L (𝓝 (base t₀)):=hb.tendsto.comp hL
  have hstrip:∀ᶠ t in L,base t∈J.Domain:=ht.eventually
    ((ComplexVerticalStrip318.strip_open J.isOpen).mem_nhds hm)
  have hc:ContinuousAt (fun z=>halfSign J upper*stripRoot J z) (base t₀):=
    continuousAt_const.mul ((stripRoot_analytic J _ hm).continuousAt)
  have hlimit:Tendsto (fun t=>halfSign J upper*stripRoot J (base t)) L
      (𝓝 (seamRoot J upper a)):=by
    simpa only [hbase,seamRoot] using hc.tendsto.comp ht
  have hevent:(fun t=>halfSign J upper*stripRoot J (base t)) =ᶠ[L] fun t=>s*lift t:=by
    filter_upwards [hinter,hstrip] with t ht hstrip'
    exact (halfSign_formula J upper (base t) ⟨hstrip',hs t ht⟩).symm.trans (he t ht)
  exact tendsto_nhds_unique (hlimit.congr' hevent) (continuousAt_const.mul hl |>.tendsto.comp hL)

/-- The algebraic end of the crossing argument: common nonzero right
lift and opposite nonzero left lifts force the actual two interval target
transitions to differ by a minus sign. All endpoint identities remain
explicit so no boundary identification is silently assumed. -/
theorem transition_flip (K:Interval i) (a b:ℝ) (sp sm u v:ℂ)
    (hsp:sp^2=1) (hsm:sm^2=1) (hu:u≠0) (hv:v≠0)
    (right_up:seamRoot J true a=sp*u) (right_down:seamRoot J false a=sm*u)
    (left_up:seamRoot K true b=sp*v) (left_down:seamRoot K false b=sm*(-v)) :
    transitionSign K= -transitionSign J := by
  have hright:=seam_transition J a
  rw [right_up,right_down] at hright
  have hleft:=seam_transition K b
  rw [left_up,left_down] at hleft
  have hr:sp=transitionSign J*sm:=by
    apply mul_right_cancel₀ hu
    simpa only [mul_assoc] using hright
  have hl:sp= -(transitionSign K*sm):=by
    apply mul_right_cancel₀ hv
    calc
      sp*v=transitionSign K*(sm*(-v)):=hleft
      _= -(transitionSign K*sm)*v:=by ring
  have hsm0:sm≠0:=by intro h;rw [h,zero_pow (by decide : 2≠0)] at hsm;norm_num at hsm
  apply mul_right_cancel₀ hsm0
  linear_combination -hr+hl
end LegendreRootArcMatching318
