module
public import OriginalCanonicalFiniteLattices318
public import KSImageFrameNorms318
public section
noncomputable section
namespace OriginalKSLatticeMetricSections318
open NumberField SectionHeight318 OriginalExcludedPlaceData318
open FinitePlacePrincipalLattice318 FinitePlacePrincipalImage318
open OriginalConstructedMetricSections318
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5, ContactRadical318.forms u v j≠0) (i : Fin 4)
  (B : ExcludedGenerators c (t u v) (hn c u v hf) i)
  (arch : InfinitePlace (K c u v) → ℝ) (harchPos : ∀ w, 0<arch w)
  (H : FrameNorms (K c u v))
  (β : FinitePlace (K c u v) → K c u v) (hβ : ∀ w, β w≠0)
  (hH : ∀ w, H.finiteNorm w=(w (β w))⁻¹)

/-- The original embedded canonical lattice, its literal multiplication
by 210, and the multiplication image of the specified Hodge lattice are
compared at every place. This is not an abstract line isomorphism premise. -/
@[expose] def LocalKSImages : Prop := ∀ w : FinitePlace (K c u v),
  (OriginalCanonicalFiniteLattices318.modelLattice c (t u v) (hn c u v hf) i B w).map
    (scalarMap w (210:K c u v))=productLattice w (β w) (β w)

/-- The consumer's full norm equality is proved from the actual lattice
images. The original good-place lattices are not caller-replaceable. -/
include hβ hH in
theorem ks_identity
    (himage : LocalKSImages c u v hf i B β)
    (harch : ∀ w, arch w=(H.arch w)^2) :
    InducedLattice318.induced (canonical c u v hf i B arch harchPos)
      (210:K c u v) (by norm_num)=InducedLattice318.square H := by
  apply KSImageFrameNorms318.induced_eq_square _ H (210:K c u v) (by norm_num)
    (OriginalCanonicalFiniteLattices318.generator c (t u v) (hn c u v hf) i B) β
    (OriginalCanonicalFiniteLattices318.generator_ne c (t u v) (hn c u v hf) i B) hβ
  · intro w
    exact OriginalCanonicalFiniteLattices318.norm_generator c (t u v) (hn c u v hf) i B w
  · exact hH
  · exact himage
  · exact harch

/-- No hks or contact-height bound is supplied to this constructor.
Excluded-place geometric provenance, the actual Hodge metric and local
KS images, Hodge degree, and original archimedean section bounds remain
explicit inputs. Thus this is not an unconditional geometric realization. -/
@[expose] def metricSections (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (himage : LocalKSImages c u v hf i B β)
    (harch : ∀ w, arch w=(H.arch w)^2)
    (hbound : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  OriginalConstructedMetricSections318.metricSections c u v hf i B arch harchPos
    H hYuan hdegree (ks_identity c u v hf i B arch harchPos H β hβ hH himage harch) hbound

/-- The final height comparison consumes precisely the above original
section object, rather than a newly selected pair with the same ratio. -/
include harchPos hβ hH in
theorem original_height (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (himage : LocalKSImages c u v hf i B β)
    (harch : ∀ w, arch w=(H.arch w)^2)
    (hbound : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    ContactHeight318.pointHeight u v<2*(hYuan-Real.log Real.pi)+120 :=
  (metricSections c u v hf i B arch harchPos H β hβ hH hYuan hdegree himage harch hbound).original_bound
end OriginalKSLatticeMetricSections318
