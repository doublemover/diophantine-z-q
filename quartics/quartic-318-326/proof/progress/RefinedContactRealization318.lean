module
public import ContactMetricSections318
public import InducedLattice318
public section
noncomputable section
namespace RefinedContactRealization318
open NumberField Height SectionHeight318 FiveContactProducer318 ContactHeight318
open SourceJacobianBound318
set_option maxHeartbeats 0

/-- Actual section and Hodge frame data over an auxiliary field. hYuan is the
shifted surface height. No contact-height or scalar KS degree identity is a field:
the KS input is equality of all local norms on the actual image lattice. -/
structure MetricSections (K:Type*) [Field K] [NumberField K] (u v:ℤ) (hYuan:ℝ) where
  a₀:K
  a₁:K
  a₀_ne:a₀≠0
  ratio:a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀
  canonical:FrameNorms K
  hodge:FrameNorms K
  hodge_degree:hodge.normalizedDegree=hYuan
  ks_image:InducedLattice318.induced canonical (210:K) (by norm_num)=
    InducedLattice318.square hodge
  arch_bound:∀(w:InfinitePlace K) i,w (![a₀,a₁] i)*canonical.arch w≤
    ContactMetricSections318.sectionBound
  finite_integral:∀(w:FinitePlace K) i,w (![a₀,a₁] i)*canonical.finiteNorm w≤1

theorem MetricSections.ks_degree {K:Type*} [Field K] [NumberField K]
    {u v:ℤ} {h:ℝ} (S:MetricSections K u v h) :
    S.canonical.normalizedDegree=2*h+Real.log 210 := by
  rw [InducedLattice318.ks_degree S.canonical S.hodge S.ks_image,S.hodge_degree]

/-- The actual original-normalized comparison, derived from the sections. -/
theorem MetricSections.original_bound {K:Type*} [Field K] [NumberField K]
    {u v:ℤ} {h:ℝ} (S:MetricSections K u v h) :
    pointHeight u v<2*(h-Real.log Real.pi)+120 := by
  apply ContactMetricSections318.contact_metric_from_sections u v S.a₀ S.a₁
    S.a₀_ne S.ratio S.canonical (h-Real.log Real.pi) _ S.arch_bound S.finite_integral
  simpa using S.ks_degree

/-- The larger shifted comparison used by the non-CM branch. -/
theorem MetricSections.shifted_bound {K:Type*} [Field K] [NumberField K]
    {u v:ℤ} {h:ℝ} (S:MetricSections K u v h) :
    pointHeight u v≤2*h+120 := by
  have hp:0≤Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hb:=S.original_bound
  linarith

/-- CM producer inputs, without any contact-height inequality. Surface height
here has the original L2 normalization. -/
structure CMInputs (u v:ℤ) where
  discriminant:ℤ
  baseDiscriminant:ℕ
  averagingDegree:ℕ
  period:Fin averagingDegree→ℂ
  fieldDegree:ℝ
  isogenyDegree:ℝ
  ellipticHeight:ℝ
  productHeight:ℝ
  surfaceHeight:ℝ
  fundamental:Int.IsFundamentalDiscr discriminant
  baseDiscriminant_ne:baseDiscriminant≠0
  prime_support:∀p:ℕ,p.Prime→p∣discriminant.natAbs→p∣baseDiscriminant
  radical_support:(CMDiscriminant318.radical baseDiscriminant:ℝ)≤support u v
  averaging_pos:1≤averagingDegree
  reduced_lower:∀i,Real.sqrt 3/2≤(period i).im
  reduced_upper:∀i,(period i).im≤Real.sqrt discriminant.natAbs/2
  silverman:ellipticHeight=(∑i,CMArchimedean318.summand (period i))/(averagingDegree:ℝ)
  product:productHeight=2*ellipticHeight
  field_pos:0<fieldDegree
  field_bound:fieldDegree≤576
  isogeny_pos:0 < isogenyDegree
  isogeny_bound:isogenyDegree≤(CMIsogeny318.Xi fieldDegree productHeight)^2
  variation:surfaceHeight≤productHeight+(1/2)*Real.log isogenyDegree

/-- Non-CM producer inputs, without any contact-height inequality. Surface
height here has the larger shifted normalization. K is the auxiliary modular
model/averaging field, not the bounded isogeny field or the section field. -/
structure NonCMInputs (K:Type*) [Field K] [NumberField K] (u v:ℤ) where
  genus:ℕ
  candidate:ℕ
  coverDegree:ℕ
  level:ℕ
  exceptionalCount:ℕ
  outsideCount:ℕ
  cusp:CuspArakelovData318.Data K genus candidate level
  finiteData:FiniteData (Fin exceptionalCount) (Fin outsideCount)
    (2^128+candidate) coverDegree level
  arakelov:SourceNonCMHeight318.ArakelovIdentifications K cusp finiteData
  genus_lower:2≤genus
  candidate_bound:candidate≤genus^3+1
  genus_degree:genus≤coverDegree
  level_pos:1≤level
  index_bound:(coverDegree:ℝ)<2^14*ActualLogWeight318.C*(support u v)^((97:ℝ)/32)
  level_bound:(level:ℝ)≤ActualLogWeight318.C*(support u v)^2
  isogenyFieldDegree:ℝ
  imageHeight:ℝ
  surfaceHeight:ℝ
  image_bound:imageHeight≤arakelov.hGR+3*(genus:ℝ)/2
  field_pos:0 < isogenyFieldDegree
  field_bound:isogenyFieldDegree≤2304*support u v
  isogeny_variation:surfaceHeight≤ imageHeight+
    8*(32*Real.log 14+Real.log isogenyFieldDegree+
      Real.log (max 1 (max (Real.log isogenyFieldDegree) imageHeight)))

/-- Reconstruct the legacy CM record only after proving its contact field
from actual sections. L need not equal the CM averaging or isogeny field. -/
def CMInputs.toLegacy {u v:ℤ} (D:CMInputs u v)
    {L:Type*} [Field L] [NumberField L]
    (S:MetricSections L u v (D.surfaceHeight+Real.log Real.pi)) : CMData u v where
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
  contact_metric := le_of_lt (by simpa using S.original_bound)

/-- Reconstruct the legacy non-CM record from independently chosen section
field L; no scalar contact estimate is supplied. -/
def NonCMInputs.toLegacy {K:Type*} [Field K] [NumberField K]
    {u v:ℤ} (D:NonCMInputs K u v)
    {L:Type*} [Field L] [NumberField L]
    (S:MetricSections L u v D.surfaceHeight) : NonCMData K u v where
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
  contact_metric := S.shifted_bound

/-- Refined global realization obligation. This is deliberately not asserted:
actual geometry must supply each producer record and actual section/Hodge data.
The section field L, model field K, CM averaging degree and controlled isogeny
field degree remain distinct. -/
@[expose] def RefinedGeometricRealization : Prop := ∀u v:ℤ, IsCoprime u v →
    (∀j:Fin 5,ContactRadical318.forms u v j≠0) →
    (∃D:CMInputs u v, ∃(L:Type) (f:Field L) (nf:@NumberField L f),
      Nonempty (@MetricSections L f nf u v (D.surfaceHeight+Real.log Real.pi))) ∨
    ∃(K:Type) (f:Field K) (nf:@NumberField K f) (D:@NonCMInputs K f nf u v),
      ∃(L:Type) (lf:Field L) (lnf:@NumberField L lf),
        Nonempty (@MetricSections L lf lnf u v D.surfaceHeight)

theorem refined_implies_legacy (h:RefinedGeometricRealization) : GeometricRealization := by
  intro u v hc hn
  rcases h u v hc hn with hm | hnc
  · obtain ⟨D,L,f,nf,⟨S⟩⟩ := hm
    letI := f
    letI := nf
    exact Or.inl ⟨D.toLegacy S⟩
  · obtain ⟨K,f,nf,D,L,lf,lnf,⟨S⟩⟩ := hnc
    letI := f
    letI := nf
    letI := lf
    letI := lnf
    exact Or.inr ⟨K,f,nf,⟨D.toLegacy S⟩⟩

/-- Exact five-contact theorem from actual refined producer data; no final
contact/Jacobian/surface854R bound is a producer field. -/
theorem five_contact_of_refined_realization (h:RefinedGeometricRealization) :
    FiveContact49Height :=
  five_contact_of_realization (refined_implies_legacy h)

end RefinedContactRealization318
