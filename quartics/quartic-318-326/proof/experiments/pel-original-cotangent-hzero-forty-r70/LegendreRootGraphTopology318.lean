module
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace LegendreRootGraphTopology318
open Set Topology LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318
variable (l:ℂ) (D:Set ℂ) (s:ℂ→ℂ)
variable (hs:∀z,s z^2=polynomial l z)

/-- The literal root graph in the unchanged topology of the actual equation. -/
@[expose] def graph (z:D) : FinitePoints l:=⟨(z.val,s z.val),hs z.val⟩
abbrev Total:={p:FinitePoints l // p.val.1∈D}
@[expose] def restricted (z:D) : Total l D:=⟨graph l D s hs z,z.property⟩
@[expose] def projection (p:Total l D) : D:=⟨p.val.val.1,p.property⟩
lemma projection_continuous : Continuous (projection l D):=
  (continuous_subtype_val.subtype_val.fst).subtype_mk _
lemma nonzero (hn:∀z∈D,polynomial l z≠0) {z:ℂ} (hz:z∈D) : s z≠0 := by
  intro h
  have he:=hs z
  rw [h,zero_pow (by decide : 2≠0)] at he
  exact hn z hz he.symm
@[expose] def ratio (p:Total l D) : ℂ:=p.val.val.2/s p.val.val.1
lemma ratio_continuous (hc:ContinuousOn s D) (hn:∀z∈D,polynomial l z≠0) :
    Continuous (ratio l D s) :=
  continuous_subtype_val.subtype_val.snd.div
    (hc.continuous_restrict.comp (projection_continuous l D))
    (fun p=>nonzero l D s hs hn p.property)
lemma restricted_continuous (hc:ContinuousOn s D) : Continuous (restricted l D s hs) :=
  ((continuous_subtype_val.prodMk hc.continuous_restrict).subtype_mk _).subtype_mk _
lemma ratio_restricted (hn:∀z∈D,polynomial l z≠0) (z:D) :
    ratio l D s (restricted l D s hs z)=1 :=
  div_self (nonzero l D s hs hn z.property)
lemma positive_iff (hn:∀z∈D,polynomial l z≠0) (p:Total l D) :
    0<(ratio l D s p).re ↔ p=restricted l D s hs (projection l D p) := by
  constructor
  · intro hp
    have he: p.val.val.2=s p.val.val.1 ∨ p.val.val.2= -s p.val.val.1 := by
      have hz:(p.val.val.2-s p.val.val.1)*(p.val.val.2+s p.val.val.1)=0 := by
        have h1:=p.val.property
        have h2:=hs p.val.val.1
        change s p.val.val.1^2=p.val.val.1*(p.val.val.1-1)*(p.val.val.1-l) at h2
        linear_combination h1-h2
      rcases mul_eq_zero.mp hz with h|h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases he with he|he
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl he
    · change 0<(p.val.val.2/s p.val.val.1).re at hp
      rw [he,neg_div,div_self (nonzero l D s hs hn p.property)] at hp
      norm_num at hp
  · intro hp
    rw [hp,ratio_restricted l D s hs hn]
    norm_num
lemma restricted_open (hc:ContinuousOn s D) (hn:∀z∈D,polynomial l z≠0) :
    IsOpenMap (restricted l D s hs) := by
  intro V hV
  have he:restricted l D s hs '' V=
      projection l D ⁻¹' V ∩ {p|0<(ratio l D s p).re} := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,(positive_iff l D s hs hn _).mpr rfl⟩
    · rintro ⟨hp,hp'⟩
      exact ⟨projection l D p,hp,((positive_iff l D s hs hn p).mp hp').symm⟩
  rw [he]
  exact (hV.preimage (projection_continuous l D)).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp (ratio_continuous l D s hs hc hn)))
lemma restricted_openEmbedding (hc:ContinuousOn s D) (hn:∀z∈D,polynomial l z≠0) :
    IsOpenEmbedding (restricted l D s hs) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨restricted_continuous l D s hs hc,?_,restricted_open l D s hs hc hn⟩
  intro z w h
  exact Subtype.ext (congrArg (fun p:Total l D=>p.val.val.1) h)
/-- No topology is transported: openness follows from the nonvanishing ratio
in the original plane equation, then the actual open base restriction. -/
theorem graph_openEmbedding (hD:IsOpen D) (hc:ContinuousOn s D)
    (hn:∀z∈D,polynomial l z≠0) : IsOpenEmbedding (graph l D s hs) := by
  have ho:IsOpen {p:FinitePoints l|p.val.1∈D}:=
    hD.preimage continuous_subtype_val.fst
  exact ho.isOpenEmbedding_subtypeVal.comp (restricted_openEmbedding l D s hs hc hn)
theorem analytic_graph_openEmbedding (hD:IsOpen D) (ha:AnalyticOnNhd ℂ s D)
    (hn:∀z∈D,polynomial l z≠0) : IsOpenEmbedding (graph l D s hs) :=
  graph_openEmbedding l D s hs hD ha.continuousOn hn
end LegendreRootGraphTopology318
