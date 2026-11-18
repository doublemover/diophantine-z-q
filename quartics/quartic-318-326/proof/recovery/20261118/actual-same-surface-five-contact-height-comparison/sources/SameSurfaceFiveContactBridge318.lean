module
public import ActualPELMetricSections318
public section
noncomputable section
namespace SameSurfaceFiveContactBridge318
open NumberField SectionHeight318 ContactHeight318 FiveContactProducer318
open ActualPELMetricSections318 RefinedContactRealization318

/-- The exact pre-existing refined normalization on each arithmetic branch. -/
@[expose] def ExactMetricBranches : Prop := ∀ u v : ℤ, IsCoprime u v →
    (∀ j : Fin 5, ContactRadical318.forms u v j≠0) →
    (∃ D : CMInputs u v, ∃ (L : Type) (f : Field L) (nf : @NumberField L f),
      Nonempty (@Datum L f nf u v (D.surfaceHeight+Real.log Real.pi))) ∨
    ∃ (K : Type) (f : Field K) (nf : @NumberField K f) (D : @NonCMInputs K f nf u v),
      ∃ (L : Type) (lf : Field L) (lnf : @NumberField L lf),
        Nonempty (@Datum L lf lnf u v D.surfaceHeight)

theorem refined_of_exact (h : ExactMetricBranches) : RefinedGeometricRealization := by
  intro u v hc hn
  rcases h u v hc hn with hm|hnc
  · obtain ⟨D,L,f,nf,⟨S⟩⟩ := hm
    letI := f
    letI := nf
    exact Or.inl ⟨D,L,f,nf,⟨metricSections S⟩⟩
  · obtain ⟨K,f,nf,D,L,lf,lnf,⟨S⟩⟩ := hnc
    letI := f
    letI := nf
    letI := lf
    letI := lnf
    exact Or.inr ⟨K,f,nf,D,L,lf,lnf,⟨metricSections S⟩⟩

theorem five_of_exact (h : ExactMetricBranches) : FiveContact49Height :=
  five_contact_of_refined_realization (refined_of_exact h)

/-- For the numerical height endpoint *both* legacy branches only require
pointHeight ≤ 2·surfaceHeight+120. No conversion equality is manufactured:
one-sided true normalization comparison suffices. -/
@[expose] def cmFromBound {u v : ℤ} (D : CMInputs u v)
    (h : pointHeight u v≤2*D.surfaceHeight+120) : CMData u v where
  discriminant := D.discriminant
  baseDiscriminant := D.baseDiscriminant
  averagingDegree := D.averagingDegree
  period := D.period
  fieldDegree := D.fieldDegree
  isogenyDegree := D.isogenyDegree
  ellipticHeight := D.ellipticHeight
  productHeight := D.productHeight
  surfaceHeight := D.surfaceHeight
  fundamental := D.fundamental
  baseDiscriminant_ne := D.baseDiscriminant_ne
  prime_support := D.prime_support
  radical_support := D.radical_support
  averaging_pos := D.averaging_pos
  reduced_lower := D.reduced_lower
  reduced_upper := D.reduced_upper
  silverman := D.silverman
  product := D.product
  field_pos := D.field_pos
  field_bound := D.field_bound
  isogeny_pos := D.isogeny_pos
  isogeny_bound := D.isogeny_bound
  variation := D.variation
  contact_metric := h

@[expose] def noncmFromBound {K : Type*} [Field K] [NumberField K] {u v : ℤ}
    (D : NonCMInputs K u v) (h : pointHeight u v≤2*D.surfaceHeight+120) : NonCMData K u v where
  genus := D.genus
  candidate := D.candidate
  coverDegree := D.coverDegree
  level := D.level
  exceptionalCount := D.exceptionalCount
  outsideCount := D.outsideCount
  cusp := D.cusp
  finiteData := D.finiteData
  arakelov := D.arakelov
  genus_lower := D.genus_lower
  candidate_bound := D.candidate_bound
  genus_degree := D.genus_degree
  level_pos := D.level_pos
  index_bound := D.index_bound
  level_bound := D.level_bound
  isogenyFieldDegree := D.isogenyFieldDegree
  imageHeight := D.imageHeight
  surfaceHeight := D.surfaceHeight
  image_bound := D.image_bound
  field_pos := D.field_pos
  field_bound := D.field_bound
  isogeny_variation := D.isogeny_variation
  contact_metric := h

/-- No prior final height estimate is a hypothesis. The other CM/non-CM
arithmetic witness and the actual marked same-surface metric datum are
still required for every admissible primitive integer pair. -/
@[expose] def DominatingMetricBranches : Prop := ∀ u v : ℤ, IsCoprime u v →
    (∀ j : Fin 5, ContactRadical318.forms u v j≠0) →
    (∃ D : CMInputs u v, ∃ (L : Type) (f : Field L) (nf : @NumberField L f) (y : ℝ),
      y-Real.log Real.pi≤D.surfaceHeight ∧ Nonempty (@Datum L f nf u v y)) ∨
    ∃ (K : Type) (f : Field K) (nf : @NumberField K f) (D : @NonCMInputs K f nf u v),
      ∃ (L : Type) (lf : Field L) (lnf : @NumberField L lf) (y : ℝ),
        y-Real.log Real.pi≤D.surfaceHeight ∧ Nonempty (@Datum L lf lnf u v y)

theorem five_of_dominating (h : DominatingMetricBranches) : FiveContact49Height := by
  apply five_contact_of_realization
  intro u v hc hn
  rcases h u v hc hn with hm|hnc
  · obtain ⟨D,L,f,nf,y,hcmp,⟨S⟩⟩:=hm
    letI := f
    letI := nf
    have hb := (metricSections S).original_bound
    exact Or.inl ⟨cmFromBound D (by linarith)⟩
  · obtain ⟨K,f,nf,D,L,lf,lnf,y,hcmp,⟨S⟩⟩:=hnc
    letI := f
    letI := nf
    letI := lf
    letI := lnf
    have hb := (metricSections S).original_bound
    exact Or.inr ⟨K,f,nf,⟨noncmFromBound D (by linarith)⟩⟩

end SameSurfaceFiveContactBridge318
