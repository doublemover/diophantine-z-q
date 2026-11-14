module
public import OriginalIntrinsicFiberFrameTransport318
public import OriginalArithmeticComplexBaseChange318
public section
noncomputable section
namespace OriginalIntrinsicAdelicSectionNorms318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry
open PELOriginalManuscriptNormalization318 OriginalArchimedeanFrameNorm318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i j : Fin 4)

lemma globalValue_independent (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    OriginalArchimedeanIntrinsicTensor318.globalValue c t hn w i s=
      OriginalArchimedeanIntrinsicTensor318.globalValue c t hn w j s := by
  rw [OriginalArchimedeanIntrinsicTensor318.globalValue_original,
    OriginalArchimedeanIntrinsicTensor318.globalValue_original,
    OriginalGlobalFrameTransport318.value_transition c t hn i j s,map_mul,
    OriginalArchimedeanIntrinsicNorm318.derivative_frame_transition c t hn w i j]
  ring

/-- Actual complex fiber transport uses the SAME analytic t tangent
frame. It preserves EVERY genuine original global section fiber. -/
@[expose] def complexComparison : OriginalArchimedeanComplexFiber318.fiber c t hn w i ≃ₗ[ℂ]
    OriginalArchimedeanComplexFiber318.fiber c t hn w j :=
  OriginalArchimedeanComplexFiber318.frame c t hn w i ≪≫ₗ
    (OriginalArchimedeanComplexFiber318.frame c t hn w j).symm
lemma complexComparison_global (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    complexComparison c t hn w i j (OriginalArchimedeanComplexFiber318.globalFiber c t hn w i s)=
      OriginalArchimedeanComplexFiber318.globalFiber c t hn w j s := by
  apply (OriginalArchimedeanComplexFiber318.frame c t hn w j).injective
  change OriginalArchimedeanComplexFiber318.frame c t hn w j
    ((OriginalArchimedeanComplexFiber318.frame c t hn w j).symm
      (OriginalArchimedeanComplexFiber318.frame c t hn w i _))=_
  rw [LinearEquiv.apply_symm_apply,OriginalArchimedeanComplexFiber318.frame_globalFiber,
    OriginalArchimedeanComplexFiber318.frame_globalFiber,globalValue_independent c t hn w i j s]

variable (hλ : lambda=2401) (hμ : mu= -343/32)
/-- The actual norm on the ENTIRE complex fiber is preserved by its full
branch comparison, not just the norms of the two distinguished vectors. -/
lemma complexComparison_norm (x : OriginalArchimedeanComplexFiber318.fiber c t hn w i) :
    letI := OriginalArchimedeanNormedFiber318.normedGroup hλ hμ c t hn w i
    letI := OriginalArchimedeanNormedFiber318.normedGroup hλ hμ c t hn w j
    ‖complexComparison c t hn w i j x‖=‖x‖ := by
  letI := OriginalArchimedeanNormedFiber318.normedGroup hλ hμ c t hn w i
  letI := OriginalArchimedeanNormedFiber318.normedGroup hλ hμ c t hn w j
  rw [OriginalArchimedeanNormedFiber318.norm_eq,OriginalArchimedeanNormedFiber318.norm_eq]
  change PeterssonSectionNorm318.quadraticNorm (density hλ hμ c t w)
    (OriginalArchimedeanComplexFiber318.frame c t hn w j
      ((OriginalArchimedeanComplexFiber318.frame c t hn w j).symm
        (OriginalArchimedeanComplexFiber318.frame c t hn w i x)))=_
  rw [LinearEquiv.apply_symm_apply]

lemma globalArchNorm_independent (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    OriginalArchimedeanIntrinsicNorm318.globalNorm hλ hμ c t hn w i s=
      OriginalArchimedeanIntrinsicNorm318.globalNorm hλ hμ c t hn w j s := by
  unfold OriginalArchimedeanIntrinsicNorm318.globalNorm
  rw [globalValue_independent c t hn w i j s]

section Finite
open OriginalAllPlaceProducedNorms318
variable (u v : ℤ) (hf : ∀ k : Fin 5,ContactRadical318.forms u v k≠0)
    (b : FinitePlace (OriginalAllPlaceProducedNorms318.K c u v))
local notation "t₀" => OriginalAllPlaceProducedNorms318.t u v
local notation "hn₀" => OriginalAllPlaceProducedNorms318.hn c u v hf
/-- Every original global section has a well-defined finite-place norm
under the actual original branch frames, including excluded places.
Combined with the genuine lattice and complex-fiber results this is an
intrinsic adelic metric on the original point line. Its identification
with global regular-model duality/Hodge/KS is STILL a separate problem. -/
lemma globalFiniteNorm_independent (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    b (ContactBicanonicalPointValue318.value c t₀ hn₀ j s)*(norms hλ hμ c u v hf j).finiteNorm b=
      b (ContactBicanonicalPointValue318.value c t₀ hn₀ i s)*(norms hλ hμ c u v hf i).finiteNorm b := by
  rw [OriginalGlobalFrameTransport318.value_transition c t₀ hn₀ i j s,map_mul,
    OriginalAllPlaceFrameCoherence318.finite_transition hλ hμ c u v hf i j b]
  have hs : b (ContactBicanonicalPointHeight318.frameScalar c t₀ hn₀ i j)≠0 :=
    (b.pos (ContactBicanonicalPointHeight318.frameScalar_ne c t₀ hn₀ i j)).ne'
  calc
    _ = (b (ContactBicanonicalPointHeight318.frameScalar c t₀ hn₀ i j)*
          (b (ContactBicanonicalPointHeight318.frameScalar c t₀ hn₀ i j))⁻¹)*
        (b (ContactBicanonicalPointValue318.value c t₀ hn₀ i s)*(norms hλ hμ c u v hf i).finiteNorm b) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs,one_mul]
end Finite
end OriginalIntrinsicAdelicSectionNorms318
