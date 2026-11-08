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
