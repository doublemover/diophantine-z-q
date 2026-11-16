module
public import OriginalExcludedModelFrames318
public import OriginalKSLatticeMetricSections318
public section
noncomputable section
namespace OriginalModelMapMetricSections318
open NumberField SectionHeight318 ActualFinitePlaceIntegers318
open FinitePlacePrincipalImage318 OriginalConstructedMetricSections318
open OriginalExcludedModelFrames318 EmbeddedLatticeFrames318
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5, ContactRadical318.forms u v j≠0) (i : Fin 4)
  (D : ModelFrames c (t u v) (hn c u v hf) i)

abbrev excluded := generators c (t u v) (hn c u v hf) i D
abbrev canonicalLattice (w : FinitePlace (K c u v)) :=
  OriginalCanonicalFiniteLattices318.modelLattice c (t u v) (hn c u v hf) i
    (excluded c u v hf i D) w

/-- Map-level residual KS input on the same embedded lattices at EVERY finite
place. The normalized comparison maps and their invertibility are supplied,
not constructed from the global Hodge family here. Their generic formula is
literally multiplication by210, including places where210 is not a unit.
This is not claimed to be the native global KS morphism before normalization. -/
structure LocalComparisons (β : FinitePlace (K c u v) → K c u v) where
  comparison : (w : FinitePlace (K c u v)) →
    canonicalLattice c u v hf i D w ≃ₗ[Integers w] productLattice w (β w) (β w)
  scalar_formula : ∀ (w : FinitePlace (K c u v)) (x : canonicalLattice c u v hf i D w),
    (comparison w x : K c u v)=(210 : K c u v)*(x : K c u v)

/-- The all-place image identity is derived from the actual normalized maps,
not supplied as a field of this interface. -/
theorem localKSImages (β : FinitePlace (K c u v) → K c u v)
    (C : LocalComparisons c u v hf i D β) :
    OriginalKSLatticeMetricSections318.LocalKSImages c u v hf i
      (excluded c u v hf i D) β := by
  intro w
  exact scalar_image_of_equiv w (C.comparison w) 210 (C.scalar_formula w)

/-- Connected per-point metric section construction. Bad-place model frames,
all normalized KS comparison maps, the specified actual Hodge norms/degree,
and archimedean geometry remain explicit inputs. Neither GeometricRealization
nor a height bound is an input; this is not an unconditional producer of them. -/
@[expose] def metricSections
    (arch : InfinitePlace (K c u v) → ℝ) (harchPos : ∀ w, 0<arch w)
    (H : FrameNorms (K c u v))
    (β : FinitePlace (K c u v) → K c u v) (hβ : ∀ w, β w≠0)
    (hH : ∀ w, H.finiteNorm w=(w (β w))⁻¹)
    (C : LocalComparisons c u v hf i D β)
    (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (harch : ∀ w, arch w=(H.arch w)^2)
    (hbound : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  OriginalKSLatticeMetricSections318.metricSections c u v hf i
    (excluded c u v hf i D) arch harchPos H β hβ hH hYuan hdegree
    (localKSImages c u v hf i D β C) harch hbound

/-- The output retains exactly the original section pair, not a substitute
chosen only to have the same ratio. -/
theorem metricSections_a0
    (arch : InfinitePlace (K c u v) → ℝ) (harchPos : ∀ w, 0<arch w)
    (H : FrameNorms (K c u v))
    (β : FinitePlace (K c u v) → K c u v) (hβ : ∀ w, β w≠0)
    (hH : ∀ w, H.finiteNorm w=(w (β w))⁻¹)
    (C : LocalComparisons c u v hf i D β)
    (hYuan : ℝ) (hdegree : H.normalizedDegree=hYuan)
    (harch : ∀ w, arch w=(H.arch w)^2)
    (hbound : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    (metricSections c u v hf i D arch harchPos H β hβ hH C hYuan hdegree harch hbound).a₀=
      ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i := rfl
end OriginalModelMapMetricSections318
