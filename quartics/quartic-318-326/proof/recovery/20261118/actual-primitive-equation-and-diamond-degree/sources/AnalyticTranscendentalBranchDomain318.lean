module
public import TranscendentalJGenericFiber318
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.DiscreteSubset
public section
noncomputable section
namespace AnalyticTranscendentalBranchDomain318
open Filter Set Topology UpperHalfPlane OpenJComplexEvaluation318
abbrev T := {τ:UpperHalfPlane // Admissible τ ∧ Transcendental ℤ (ActualQJ318.jInvariant τ)}
abbrev Holo (f:ℂ→ℂ) := AnalyticOnNhd ℂ f upperHalfPlaneSet

/-- Any two holomorphic numerators whose product vanishes at all the
transcendental arithmetic periods have one identically zero numerator.
Proof uses countability of a discrete zero set and actual large j-values,
not continuation from a single chosen transcendental value. -/
private theorem zeros_countable {f:ℂ→ℂ} (hf:Holo f) (x:UpperHalfPlane) (hx:f x≠0) :
    {τ:UpperHalfPlane | f τ=0}.Countable := by
  let Z := {τ:UpperHalfPlane | f τ=0}
  have hd : IsDiscrete Z := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro τ hτ
    have hn : ¬∀ᶠz in 𝓝 (τ:ℂ),f z=0 := by
      intro hvan
      have he := hf.eqOn_of_preconnected_of_eventuallyEq
        (show Holo (fun _=>0) from analyticOnNhd_const)
        (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hvan
      exact hx (he x.im_pos)
    have hp := ((hf (τ:ℂ) τ.im_pos).eventually_eq_or_eventually_ne
      (show AnalyticAt ℂ (fun _=>(0:ℂ)) (τ:ℂ) from analyticAt_const)).resolve_left hn
    have hpo : ∀ᶠz in 𝓝 (τ:ℂ),z≠(τ:ℂ)→f z≠0 := by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using eventually_nhdsWithin_iff.mp hp
    obtain ⟨U,hU,hUo,hUτ⟩ := mem_nhds_iff.mp hpo
    refine ⟨(fun t:UpperHalfPlane=>(t:ℂ)) ⁻¹' U,hUo.preimage continuous_coe,?_⟩
    ext t
    constructor
    · rintro ⟨ht,hz⟩
      apply Set.mem_singleton_iff.mpr
      apply UpperHalfPlane.coe_injective
      by_contra hne
      exact hU ht hne hz
    · rintro rfl
      exact ⟨hUτ,hτ⟩
  letI : DiscreteTopology Z := isDiscrete_iff_discreteTopology.mp hd
  exact separableSpace_iff_countable.mp (inferInstance : SeparableSpace Z)

theorem split {F G:ℂ→ℂ} (hF:Holo F) (hG:Holo G)
    (hzero:∀p:T,F (p.val:ℂ)*G (p.val:ℂ)=0) :
    (∀τ:UpperHalfPlane,F τ=0) ∨ (∀τ:UpperHalfPlane,G τ=0) := by
  by_contra! hn
  obtain ⟨⟨t,ht⟩,⟨s,hs⟩⟩ := hn
  let Z := {τ:UpperHalfPlane| F τ=0} ∪ {τ:UpperHalfPlane|G τ=0}
  have hc : Z.Countable := (zeros_countable hF t ht).union (zeros_countable hG s hs)
  let bad := (ActualQJ318.jInvariant '' Z) ∪ {z:ℂ|IsAlgebraic ℤ z}
  have hb : bad.Countable := (hc.image _).union (Algebraic.countable ℤ ℂ)
  obtain ⟨M,hM⟩ := ActualLargeJRealization318.all_large
  let line (x:ℝ) : ℂ := ⟨x,max M 1728+1⟩
  have hi : Function.Injective line := fun _ _ h=>congrArg Complex.re h
  obtain ⟨x,hx⟩ : ∃x:ℝ,line x∉bad := by
    by_contra! hh
    exact Set.not_countable_univ (α:=ℝ) ((hb.preimage hi).mono (fun a _=>hh a))
  have hnorm := Complex.abs_im_le_norm (line x)
  change |max M 1728+1|≤‖line x‖ at hnorm
  rw [abs_of_nonneg (by linarith [le_max_right M (1728:ℝ)] : 0≤max M 1728+1)] at hnorm
  obtain ⟨τ,he⟩ := hM (line x) (by linarith [le_max_left M (1728:ℝ)])
  have hbig : (1728:ℝ)<‖ActualQJ318.jInvariant τ‖ := by rw [he];linarith [le_max_right M (1728:ℝ)]
  have ha : Admissible τ := by
    constructor <;> intro hh <;> rw [hh] at hbig <;> norm_num at hbig
  have htr : Transcendental ℤ (ActualQJ318.jInvariant τ) := fun h=>hx (Or.inr (he ▸ h))
  have hz : τ∈Z := mul_eq_zero.mp (hzero ⟨τ,ha,htr⟩)
  exact hx (Or.inl ⟨τ,hz,he⟩)

/-- A meromorphic expression on the upper half-plane represented by two
global holomorphic functions; denominator is nonzero on ALL the arithmetic
test periods. We require no single rational expression for all holomorphic
functions, and allow E₆ to vanish at excluded periods. -/
def Rep (a:T→ℂ) : Prop := ∃F G:ℂ→ℂ,Holo F ∧ Holo G ∧
  ∀p:T,G (p.val:ℂ)≠0 ∧ a p=F (p.val:ℂ)/G (p.val:ℂ)

theorem rep_holo (F:ℂ→ℂ) (hf:Holo F) : Rep (fun p=>F (p.val:ℂ)) := by
  exact ⟨F,fun _=>1,hf,analyticOnNhd_const,fun p=>⟨one_ne_zero,(div_one _).symm⟩⟩

theorem rep_const (z:ℂ) : Rep (fun _=>z) := rep_holo (fun _=>z) analyticOnNhd_const

theorem rep_add {a b:T→ℂ} (ha:Rep a) (hb:Rep b) : Rep (fun p=>a p+b p) := by
  obtain ⟨F,G,hF,hG,h⟩ := ha
  obtain ⟨U,V,hU,hV,k⟩ := hb
  refine ⟨fun z=>F z*V z+U z*G z,fun z=>G z*V z,
    fun z hz=>((hF z hz).mul (hV z hz)).add ((hU z hz).mul (hG z hz)),
    fun z hz=>(hG z hz).mul (hV z hz),?_⟩
  intro p
  exact ⟨mul_ne_zero (h p).1 (k p).1,by rw [(h p).2,(k p).2];field_simp [(h p).1,(k p).1] <;> ring⟩

theorem rep_mul {a b:T→ℂ} (ha:Rep a) (hb:Rep b) : Rep (fun p=>a p*b p) := by
  obtain ⟨F,G,hF,hG,h⟩ := ha
  obtain ⟨U,V,hU,hV,k⟩ := hb
  exact ⟨fun z=>F z*U z,fun z=>G z*V z,fun z hz=>(hF z hz).mul (hU z hz),
    fun z hz=>(hG z hz).mul (hV z hz),fun p=>⟨mul_ne_zero (h p).1 (k p).1,
      by rw [(h p).2,(k p).2,div_mul_div_comm]⟩⟩

theorem rep_div {a b:T→ℂ} (ha:Rep a) (hb:Rep b) (hn:∀p,b p≠0) :
    Rep (fun p=>a p/b p) := by
  obtain ⟨U,V,hU,hV,k⟩ := hb
  have hi : Rep (fun p=>(b p)⁻¹) := by
    refine ⟨V,U,hV,hU,?_⟩
    intro p
    have hu : U (p.val:ℂ)≠0 := fun h=>hn p (by rw [(k p).2,h,zero_div])
    exact ⟨hu,by rw [(k p).2,inv_div]⟩
  simpa only [div_eq_mul_inv] using rep_mul ha hi

theorem rep_pow {a:T→ℂ} (ha:Rep a) (n:ℕ) : Rep (fun p=>a p^n) := by
  induction n with
  | zero=>simpa only [pow_zero] using rep_const 1
  | succ n ih=>simpa only [pow_succ] using rep_mul ih ha

theorem rep_split {a b:T→ℂ} (ha:Rep a) (hb:Rep b) (hz:∀p,a p*b p=0) :
    (∀p,a p=0) ∨ (∀p,b p=0) := by
  obtain ⟨F,G,hF,hG,h⟩ := ha
  obtain ⟨U,V,hU,hV,k⟩ := hb
  have hh := split hF hU (fun p=>by
    have he := hz p
    rw [(h p).2,(k p).2,div_mul_div_comm] at he
    exact (div_eq_zero_iff.mp he).resolve_right (mul_ne_zero (h p).1 (k p).1))
  rcases hh with hh|hh
  · exact Or.inl (fun p=>by rw [(h p).2,hh p.val,zero_div])
  · exact Or.inr (fun p=>by rw [(k p).2,hh p.val,zero_div])
end AnalyticTranscendentalBranchDomain318
