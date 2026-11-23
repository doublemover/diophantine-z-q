module
public import SelectedSameADirectBicanonicalHeight318

/-! Placewise image-lattice and rescaling comparisons for the direct
bicanonical receiver. The finite norm comparison applies to ξ=Ψ(η²) on
the genuinely pulled dualizing square; the archimedean comparison uses
the raw isometry on that same vector, not the normalized inverse. -/
public section
noncomputable section

namespace SelectedSameABicanonicalYuanFrame318

open NumberField SectionHeight318
variable {F : Type*} [Field F] [NumberField F]

private theorem frameNorms_eq (A B : FrameNorms F)
    (ha : ∀ v, A.arch v = B.arch v)
    (hf : ∀ v, A.finiteNorm v = B.finiteNorm v) : A = B := by
  cases A with
  | mk Aa Af Aap Afp As =>
    cases B with
    | mk Ba Bf Bap Bfp Bs =>
      change ∀ v, Aa v = Ba v at ha
      change ∀ v, Af v = Bf v at hf
      cases funext ha
      cases funext hf
      rfl

/-- The finite quotient is derived on the original model using the raw
coefficient's two divisibility relations, then pulled to the actual traits.
The arch identity is the tensor-square raw isometry on the same frame pair. -/
theorem induced_eq_square (Xi H : FrameNorms F)
    (ha : ∀ v, Xi.arch v = H.arch v ^ 2)
    (hf : ∀ v : FinitePlace F, Xi.finiteNorm v / v.val (210 : F) = H.finiteNorm v ^ 2) :
    InducedLattice318.induced Xi (210 : F) (by norm_num) = InducedLattice318.square H :=
  frameNorms_eq _ _ ha hf

/-- Only one scalar relates the two genuine frames of D². Its same generic
identity Q=c·ξ gives the indicated finite and infinite norm transformations. -/
theorem rescale_eq (Q Xi : FrameNorms F) (c : F) (hc : c ≠ 0)
    (ha : ∀ v : InfinitePlace F, Q.arch v = v.val c * Xi.arch v)
    (hf : ∀ v : FinitePlace F, Q.finiteNorm v = v.val c * Xi.finiteNorm v) :
    Q = Xi.rescale c hc :=
  frameNorms_eq _ _ ha hf

/-- Same-line consumer at actual placewise readouts; no extra equality of
adelic records or separate bicanonical degree assumption is needed. -/
theorem height_of_raw_ks_places (t : ℚ) (Q Xi H : FrameNorms F) (c : F) (hc : c ≠ 0)
    (rescaleArch : ∀ v : InfinitePlace F, Q.arch v = v.val c * Xi.arch v)
    (rescaleFinite : ∀ v : FinitePlace F, Q.finiteNorm v = v.val c * Xi.finiteNorm v)
    (rawArch : ∀ v, Xi.arch v = H.arch v ^ 2)
    (rawFinite : ∀ v : FinitePlace F, Xi.finiteNorm v / v.val (210 : F) = H.finiteNorm v ^ 2)
    (harch : ∀ v : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (v (t : F)) ≤ U ∧ 64 ≤ f ∧ Q.arch v = 4 / (U * f))
    (hfinite : ∀ (v : FinitePlace F) i,
      v (SelectedSameADirectBicanonicalHeight318.coefficients t i) * Q.finiteNorm v ≤ 1) :
    Height.logHeight₁ (t / 32) < 2 * H.normalizedDegree + 11 :=
  SelectedSameADirectBicanonicalHeight318.height_of_raw_ks t Q Xi H c hc
    (rescale_eq Q Xi c hc rescaleArch rescaleFinite)
    (induced_eq_square Xi H rawArch rawFinite) harch hfinite

end SelectedSameABicanonicalYuanFrame318

#print axioms SelectedSameABicanonicalYuanFrame318.height_of_raw_ks_places
