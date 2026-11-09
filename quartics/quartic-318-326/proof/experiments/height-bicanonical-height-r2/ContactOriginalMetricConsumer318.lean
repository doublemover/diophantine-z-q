module
public import ContactBicanonicalPointHeight318
public import RefinedContactRealization318
public section
noncomputable section
namespace ContactOriginalMetricConsumer318
open NumberField SectionHeight318 ContactBicanonicalPointHeight318
set_option maxHeartbeats 400000
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
    (hf : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0)

abbrev coordinate : ℚ := 32 * ((u : ℚ) / (v : ℚ))
abbrev PointField := RationalContactPoint318.PointField c (coordinate u v)
abbrev avoidance := RationalContactPoint318.parameters_ne_of_forms c u v hf

/-- Exact height of the original homogeneous contact point, using the actual
scaled sections and undoing precisely the coordinate factor 32. -/
theorem normalized_original_height (i : Fin 4) :
    Height.logHeight ![a0 c (coordinate u v) (avoidance c u v hf) i,
      a1 c (coordinate u v) (avoidance c u v hf) i / 32] /
      (fieldDegree (PointField c u v) : ℝ) = ContactHeight318.pointHeight u v := by
  have hr : a1 c (coordinate u v) (avoidance c u v hf) i / 32 =
      (((u : ℚ) / (v : ℚ) : ℚ) : PointField c u v) *
        a0 c (coordinate u v) (avoidance c u v hf) i := by
    rw [ratio]
    unfold coordinate
    push_cast
    ring
  rw [SectionHeight318.rational_ratio_height _ _ ((u : ℚ) / (v : ℚ))
    (a0_ne c _ _ i) hr, FiveContactProducer318.pointHeight_eq_contact_height,
    DetectorHeightTransfer318.rational_height_eq]

/-- The section height theorem applied to the actual evaluated scaled pair.
The frame and both all-place estimates remain explicit geometric inputs. -/
theorem section_height (i : Fin 4) (F : FrameNorms (PointField c u v)) (C : ℝ)
    (harch : ∀ (w : InfinitePlace (PointField c u v)) k,
      w (![a0 c (coordinate u v) (avoidance c u v hf) i,
        a1 c (coordinate u v) (avoidance c u v hf) i] k) * F.arch w ≤ C)
    (hfinite : ∀ (w : FinitePlace (PointField c u v)) k,
      w (![a0 c (coordinate u v) (avoidance c u v hf) i,
        a1 c (coordinate u v) (avoidance c u v hf) i] k) * F.finiteNorm w ≤ 1) :
    Height.logHeight₁ (coordinate u v) ≤ F.normalizedDegree + Real.log C :=
  SectionHeight318.rational_section_height _ _ _
    (a0_ne c _ _ i) (ratio c _ _ i) F C harch hfinite

/-- Assemble the existing metric consumer with its two scalars fixed to the
actual original-point evaluation. This does not construct the metric inputs,
identify a PEL field, or assert that the inputs exist. -/
@[expose] def metricSections (i : Fin 4)
    (canonical hodge : FrameNorms (PointField c u v)) (hYuan : ℝ)
    (hdegree : hodge.normalizedDegree = hYuan)
    (hks : InducedLattice318.induced canonical (210 : PointField c u v)
      (by norm_num) = InducedLattice318.square hodge)
    (harch : ∀ (w : InfinitePlace (PointField c u v)) k,
      w (![a0 c (coordinate u v) (avoidance c u v hf) i,
        a1 c (coordinate u v) (avoidance c u v hf) i] k) * canonical.arch w ≤
          ContactMetricSections318.sectionBound)
    (hfinite : ∀ (w : FinitePlace (PointField c u v)) k,
      w (![a0 c (coordinate u v) (avoidance c u v hf) i,
        a1 c (coordinate u v) (avoidance c u v hf) i] k) * canonical.finiteNorm w ≤ 1) :
    RefinedContactRealization318.MetricSections (PointField c u v) u v hYuan where
  a₀ := a0 c (coordinate u v) (avoidance c u v hf) i
  a₁ := a1 c (coordinate u v) (avoidance c u v hf) i
  a₀_ne := a0_ne c _ _ i
  ratio := ContactBicanonicalPointHeight318.ratio c _ _ i
  canonical := canonical
  hodge := hodge
  hodge_degree := hdegree
  ks_image := hks
  arch_bound := harch
  finite_integral := hfinite

end ContactOriginalMetricConsumer318
