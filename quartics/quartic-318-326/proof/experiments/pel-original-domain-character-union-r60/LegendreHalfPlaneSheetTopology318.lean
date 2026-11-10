module
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace LegendreHalfPlaneSheetTopology318
open Set Topology
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318
set_option maxHeartbeats 1200000
variable (l:ℂ) (hl:l.im=0) (upper:Bool)

/-- The target has its ORIGINAL subspace topology as literal complex
points of the affine equation, restricted to the whole inverse halfplane.
No topology is transported from the source cover or a pair of sheets. -/
abbrev Total:={p:FinitePoints l // p.val.1∈domain upper}
@[expose] def projection (p:Total l upper) : domain upper:=⟨p.val.val.1,p.property⟩
@[expose] def sheet (positive:Bool) (z:domain upper) : Total l upper:=
  if positive then ⟨positivePoint l hl upper z.val,z.property⟩
  else ⟨negativePoint l hl upper z.val,z.property⟩

lemma projection_sheet (positive:Bool) (z:domain upper) :
    projection l upper (sheet l hl upper positive z)=z := by
  cases positive <;> rfl
lemma projection_continuous : Continuous (projection l upper) := by
  change Continuous (fun p:Total l upper=>
    (⟨p.val.val.1,p.property⟩:domain upper))
  exact (continuous_subtype_val.subtype_val.fst).subtype_mk _
lemma root_continuous : Continuous (fun z:domain upper=>root l hl upper z.val) :=
  (root_analytic l hl upper).continuousOn.continuous_restrict
lemma sheet_continuous (positive:Bool) : Continuous (sheet l hl upper positive) := by
  cases positive
  · change Continuous (fun z:domain upper=>
      (⟨⟨(z.val,-root l hl upper z.val),_⟩,z.property⟩:Total l upper))
    exact ((continuous_subtype_val.prodMk (root_continuous l hl upper).neg).subtype_mk _).subtype_mk _
  · change Continuous (fun z:domain upper=>
      (⟨⟨(z.val,root l hl upper z.val),_⟩,z.property⟩:Total l upper))
    exact ((continuous_subtype_val.prodMk (root_continuous l hl upper)).subtype_mk _).subtype_mk _

/-- A continuous distinguishing coordinate on the actual plane. Its values
are exactly plus/minus one; it detects OPEN sheet images in the existing
topology rather than defining a new topology to make them open. -/
@[expose] def ratio (p:Total l upper) : ℂ:=p.val.val.2/root l hl upper p.val.val.1
lemma ratio_continuous : Continuous (ratio l hl upper) := by
  have hn:∀p:Total l upper,root l hl upper p.val.val.1≠0:=
    fun p=>root_nonzero l hl upper _ p.property
  exact continuous_subtype_val.subtype_val.snd.div
    ((root_continuous l hl upper).comp (projection_continuous l upper)) hn
lemma ratio_sheet (positive:Bool) (z:domain upper) :
    ratio l hl upper (sheet l hl upper positive z)=if positive then 1 else -1 := by
  have hn:=root_nonzero l hl upper z.val z.property
  cases positive
  · change -root l hl upper z.val/root l hl upper z.val=(-1:ℂ)
    rw [neg_div,div_self hn]
  · change root l hl upper z.val/root l hl upper z.val=(1:ℂ)
    exact div_self hn

lemma all_sheets (p:Total l upper) :
    p=sheet l hl upper true (projection l upper p) ∨
    p=sheet l hl upper false (projection l upper p) := by
  rcases (sheet_exhaustion l hl upper p.val p.property).1 with h|h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

@[expose] def sideSet (positive:Bool) : Set (Total l upper):=
  {p|0<if positive then (ratio l hl upper p).re else -(ratio l hl upper p).re}
lemma sideSet_open (positive:Bool) : IsOpen (sideSet l hl upper positive) := by
  apply isOpen_lt continuous_const
  cases positive
  · exact (Complex.continuous_re.comp (ratio_continuous l hl upper)).neg
  · exact Complex.continuous_re.comp (ratio_continuous l hl upper)
lemma sheet_mem_side (positive:Bool) (z:domain upper) :
    sheet l hl upper positive z∈sideSet l hl upper positive := by
  change 0<if positive then (ratio l hl upper (sheet l hl upper positive z)).re
    else -(ratio l hl upper (sheet l hl upper positive z)).re
  rw [ratio_sheet]
  cases positive <;> norm_num

lemma in_side_iff (positive:Bool) (p:Total l upper) :
    p∈sideSet l hl upper positive ↔ p=sheet l hl upper positive (projection l upper p) := by
  constructor
  · intro h
    rcases all_sheets l hl upper p with hp|hp
    · cases positive
      · change 0< -(ratio l hl upper p).re at h
        rw [hp,ratio_sheet] at h
        norm_num at h
      · exact hp
    · cases positive
      · exact hp
      · change 0<(ratio l hl upper p).re at h
        rw [hp,ratio_sheet] at h
        norm_num at h
  · intro hp
    rw [hp]
    exact sheet_mem_side l hl upper positive _

/-- Entire sheet images of ANY open subset of the actual halfplane are
open in the original finite-equation subspace topology. -/
lemma sheet_image (positive:Bool) (V:Set (domain upper)) :
    sheet l hl upper positive '' V=
      (projection l upper) ⁻¹' V ∩ sideSet l hl upper positive := by
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨by simpa only [mem_preimage,projection_sheet] using hz,
      sheet_mem_side l hl upper positive z⟩
  · rintro ⟨hp,hs⟩
    exact ⟨projection l upper p,hp,((in_side_iff l hl upper positive p).mp hs).symm⟩
lemma sheet_open (positive:Bool) : IsOpenMap (sheet l hl upper positive) := by
  intro V hV
  rw [sheet_image]
  exact (hV.preimage (projection_continuous l upper)).inter (sideSet_open l hl upper positive)

/-- The two target sheets are genuine open embeddings for the unchanged
plane topology, not only continuous parameterizations of its point set. -/
theorem sheet_openEmbedding (positive:Bool) : IsOpenEmbedding (sheet l hl upper positive) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨sheet_continuous l hl upper positive,?_,sheet_open l hl upper positive⟩
  intro z w h
  simpa only [projection_sheet] using congrArg (projection l upper) h
/-- The genuine target over the whole halfplane is a disjoint union of its
TWO constructed analytic sheets in its unchanged plane topology. -/
@[expose] def fromSum : domain upper ⊕ domain upper → Total l upper:=
  Sum.elim (sheet l hl upper true) (sheet l hl upper false)
lemma fromSum_continuous : Continuous (fromSum l hl upper):=
  continuous_sum_dom.mpr ⟨sheet_continuous l hl upper true,sheet_continuous l hl upper false⟩
lemma fromSum_bijective : Function.Bijective (fromSum l hl upper) := by
  constructor
  · intro z w h
    cases z with
    | inl z=>
      cases w with
      | inl w=>exact congrArg Sum.inl ((sheet_openEmbedding l hl upper true).injective h)
      | inr w=>
        have hr:=congrArg (ratio l hl upper) h
        change ratio l hl upper (sheet l hl upper true z)=ratio l hl upper (sheet l hl upper false w) at hr
        rw [ratio_sheet,ratio_sheet] at hr
        norm_num at hr
    | inr z=>
      cases w with
      | inl w=>
        have hr:=congrArg (ratio l hl upper) h
        change ratio l hl upper (sheet l hl upper false z)=ratio l hl upper (sheet l hl upper true w) at hr
        rw [ratio_sheet,ratio_sheet] at hr
        norm_num at hr
      | inr w=>exact congrArg Sum.inr ((sheet_openEmbedding l hl upper false).injective h)
  · intro p
    rcases all_sheets l hl upper p with hp|hp
    · exact ⟨Sum.inl (projection l upper p),hp.symm⟩
    · exact ⟨Sum.inr (projection l upper p),hp.symm⟩
lemma fromSum_open : IsOpenMap (fromSum l hl upper) := by
  intro V hV
  have he:fromSum l hl upper '' V=
      sheet l hl upper true '' (Sum.inl ⁻¹' V) ∪ sheet l hl upper false '' (Sum.inr ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      cases z with
      | inl z=>exact Or.inl ⟨z,hz,rfl⟩
      | inr z=>exact Or.inr ⟨z,hz,rfl⟩
    · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
      · exact ⟨Sum.inl z,hz,rfl⟩
      · exact ⟨Sum.inr z,hz,rfl⟩
  rw [he]
  exact (sheet_open l hl upper true _ (hV.preimage continuous_inl)).union
    (sheet_open l hl upper false _ (hV.preimage continuous_inr))

@[expose] def homeomorph : domain upper ⊕ domain upper ≃ₜ Total l upper:=
  (Equiv.ofBijective (fromSum l hl upper) (fromSum_bijective l hl upper)).toHomeomorphOfContinuousOpen
    (fromSum_continuous l hl upper) (fromSum_open l hl upper)
end LegendreHalfPlaneSheetTopology318
