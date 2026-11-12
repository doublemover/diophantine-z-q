module
public import OriginalConstructedArchimedeanSections318
public import OriginalZoomDifferentialNorm318
public import OriginalArchimedeanNormedFiber318
public section
noncomputable section
namespace OriginalAllPlaceProducedNorms318
open NumberField SectionHeight318 PELOriginalManuscriptNormalization318
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
abbrev K := ContactOriginalMetricConsumer318.PointField c u v
abbrev t := ContactOriginalMetricConsumer318.coordinate u v
abbrev hn := ContactOriginalMetricConsumer318.avoidance c u v hf

/-- A fully PRODUCED all-place frame-norm family: good-place original
model lattices, excluded-place genuine integral cotangent zoom fibers,
and the original analytic Poincare norm. It is not asserted to be the
canonical lattice on a global proper regular arithmetic model. -/
@[expose] def norms : FrameNorms (K c u v) :=
  OriginalAllPrimeConstructedMetric318.canonical c u v hf i
    (OriginalConstructedArchimedeanSections318.arch hλ hμ c u v i)
    (OriginalConstructedArchimedeanSections318.arch_pos hλ hμ c u v hf i)
lemma arch_bound (w : InfinitePlace (K c u v)) (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
      ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*
        (norms hλ hμ c u v hf i).arch w≤ContactMetricSections318.sectionBound :=
  OriginalArchimedeanFrameNorm318.all_sections hλ hμ c (t u v) (hn c u v hf) w i n
lemma finite_bound (w : FinitePlace (K c u v)) (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
      ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*
        (norms hλ hμ c u v hf i).finiteNorm w≤1 :=
  OriginalAllPrimeConstructedMetric318.finite_integral c u v hf i _ _ w n

lemma good_finite (w : FinitePlace (K c u v))
    (hw : w (ContactArithmeticDenominator318.denominator c:K c u v)=1) :
    (norms hλ hμ c u v hf i).finiteNorm w=
      OriginalGoodPlaceCotangentNorms318.finiteNorm c (t u v) (hn c u v hf) w hw i :=
  OriginalAllPrimeConstructedMetric318.canonical_good c u v hf i _ _ w hw

/-- Exact excluded-place differential square, including every place over
2,3,5,7. This identifies the produced LOCAL lattice, not global KS. -/
lemma excluded_finite (w : FinitePlace (K c u v))
    (hw : w (ContactArithmeticDenominator318.denominator c:K c u v)≠1) :
    (norms hλ hμ c u v hf i).finiteNorm w=
      (w (OriginalZoomDifferentialFrameScalar318.scalar c (t u v) w
        (OriginalContactAllPrimeNeighborhood318.data c u v w)
        (OriginalContactAllPrimeNeighborhood318.input c u v hf w) i))^2 := by
  change OriginalFiniteNormAssembly318.finiteNorm c (t u v) (hn c u v hf) i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) w=_
  rw [OriginalFiniteNormAssembly318.finiteNorm,dif_neg hw]
  exact OriginalZoomDifferentialNorm318.excluded_norm c i u v hf ⟨w,hw⟩

/-- Honest original height bound in the degree of the fully constructed
adelic norm family. No Hodge degree or KS equality is used here. -/
theorem height_bound : Height.logHeight₁ (t u v)≤
    (norms hλ hμ c u v hf i).normalizedDegree+Real.log ContactMetricSections318.sectionBound :=
  SectionHeight318.rational_section_height _ _ (t u v)
    (ContactBicanonicalPointHeight318.a0_ne c (t u v) (hn c u v hf) i)
    (ContactBicanonicalPointHeight318.ratio c (t u v) (hn c u v hf) i)
    (norms hλ hμ c u v hf i) ContactMetricSections318.sectionBound
    (arch_bound hλ hμ c u v hf i) (finite_bound hλ hμ c u v hf i)
end OriginalAllPlaceProducedNorms318
