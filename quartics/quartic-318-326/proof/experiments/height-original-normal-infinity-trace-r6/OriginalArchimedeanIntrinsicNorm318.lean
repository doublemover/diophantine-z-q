module
public import OriginalArchimedeanIntrinsicTensor318
public section
noncomputable section
namespace OriginalArchimedeanIntrinsicNorm318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanMarkedPoint318
open OriginalArchimedeanSectionCoefficient318 OriginalArchimedeanFrameNorm318
open OriginalArchimedeanIntrinsicTensor318 AlgebraicGeometry PeterssonSectionNorm318
open PELOriginalManuscriptNormalization318
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t))

/-- Norm of ANY true global intrinsic bicanonical section, through the
whole algebraic tensor fiber and actual t tangent functional. -/
@[expose] def globalNorm (i : Fin 4) (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : ℝ :=
  quadraticNorm (density hλ hμ c t w) (globalValue c t hn w i s)
lemma globalNorm_original (i : Fin 4) (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    globalNorm hλ hμ c t hn w i s=
      w (ContactBicanonicalPointValue318.value c t hn i s)*frameNorm hλ hμ c t w i := by
  rw [globalNorm,globalValue_original]
  exact (scalar_norm hλ hμ c t w i _).symm

/-- Exact evaluated transition between the ORIGINAL four branch-square
frames, obtained from their common nonzero original global section. -/
lemma derivative_frame_transition (i j : Fin 4) :
    branchDerivative c t w i^2=
      w.embedding (ContactBicanonicalPointHeight318.frameScalar c t hn i j)*
        branchDerivative c t w j^2 := by
  have he := (scaled_coordinates c t hn w i).1.trans (scaled_coordinates c t hn w j).1.symm
  rw [ContactBicanonicalPointHeight318.frameScalar_a0 c t hn i j,map_mul] at he
  apply mul_left_cancel₀ (w.embedding.injective.ne (ContactBicanonicalPointHeight318.a0_ne c t hn i))
  calc
    _ = (w.embedding (ContactBicanonicalPointHeight318.frameScalar c t hn i j)*
        w.embedding (ContactBicanonicalPointHeight318.a0 c t hn i))*branchDerivative c t w j^2 := he
    _ = _ := by ring

/-- The positive archimedean norms obey the literal original frame
transition. Hence selecting a different branch frame does not change
the underlying metric or either distinguished section norm. -/
lemma frameNorm_transition (i j : Fin 4) :
    frameNorm hλ hμ c t w i=
      w (ContactBicanonicalPointHeight318.frameScalar c t hn i j)*frameNorm hλ hμ c t w j := by
  unfold frameNorm
  rw [derivative_frame_transition c t hn w i j,quadraticNorm_mul,InfinitePlace.norm_embedding_eq]
lemma scaled0_frame_independent (i j : Fin 4) :
    globalNorm hλ hμ c t hn w i (ContactScaledBicanonicalPoint318.scaledQ0 c)=
      globalNorm hλ hμ c t hn w j (ContactScaledBicanonicalPoint318.scaledQ0 c) := by
  simp only [globalNorm,globalValue_scaled0]
lemma scaled1_frame_independent (i j : Fin 4) :
    globalNorm hλ hμ c t hn w i (ContactScaledBicanonicalPoint318.scaledQ1 c)=
      globalNorm hλ hμ c t hn w j (ContactScaledBicanonicalPoint318.scaledQ1 c) := by
  simp only [globalNorm,globalValue_scaled1]
lemma global_scaled_bounds (i : Fin 4) :
    globalNorm hλ hμ c t hn w i (ContactScaledBicanonicalPoint318.scaledQ0 c)≤
      ContactMetricSections318.sectionBound ∧
    globalNorm hλ hμ c t hn w i (ContactScaledBicanonicalPoint318.scaledQ1 c)≤
      ContactMetricSections318.sectionBound := by
  rw [globalNorm_original,globalNorm_original]
  exact section_bounds hλ hμ c t hn w i
end OriginalArchimedeanIntrinsicNorm318
