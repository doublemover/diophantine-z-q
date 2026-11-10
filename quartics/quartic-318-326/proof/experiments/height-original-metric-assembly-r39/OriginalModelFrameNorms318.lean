module
public import OriginalFiniteNormAssembly318
public section
noncomputable section
namespace OriginalModelFrameNorms318
open NumberField OriginalPointFinitePlaceRoots318 OriginalExcludedPlaceData318
set_option maxHeartbeats 800000
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (B : ExcludedGenerators c t hn i)
  (arch : InfinitePlace (K c t) → ℝ) (harch : ∀ w, 0<arch w)

/-- A genuine FrameNorms record whose entire good finite part and global
finite-support proof have been constructed from the original model.
The residual archimedean and excluded-place data remain displayed inputs. -/
@[expose] def frame : SectionHeight318.FrameNorms (K c t) where
  arch := arch
  finiteNorm := OriginalFiniteNormAssembly318.finiteNorm c t hn i B
  arch_pos := harch
  finite_pos := OriginalFiniteNormAssembly318.finiteNorm_pos c t hn i B
  finite_support := OriginalFiniteNormAssembly318.finite_support c t hn i B

/-- The original section-height theorem now consumes the constructed
finite geometry, rather than taking all finite-place inequalities as input. -/
theorem section_height (C : ℝ)
    (hbound : ∀ (w : InfinitePlace (K c t)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c t hn i,
        ContactBicanonicalPointHeight318.a1 c t hn i] n)*arch w≤C) :
    Height.logHeight₁ t≤(frame c t hn i B arch harch).normalizedDegree+Real.log C :=
  SectionHeight318.rational_section_height _ _ t
    (ContactBicanonicalPointHeight318.a0_ne c t hn i) (ContactBicanonicalPointHeight318.ratio c t hn i)
    (frame c t hn i B arch harch) C hbound (OriginalFiniteNormAssembly318.original_bound c t hn i B)
end OriginalModelFrameNorms318
