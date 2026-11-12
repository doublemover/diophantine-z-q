module
public import OriginalAllPlaceProducedNorms318
public import OriginalArchimedeanIntrinsicNorm318
public section
noncomputable section
namespace OriginalAllPlaceFrameCoherence318
open NumberField SectionHeight318 PELOriginalManuscriptNormalization318
open OriginalAllPlaceProducedNorms318 ContactBicanonicalPointHeight318
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i j : Fin 4)

/-- The actual excluded generator uses one and the same integral q0
coefficient for all original branch frames. This is an equality of
field elements, before applying valuations or comparing degrees. -/
lemma excluded_generator_transition (b : OriginalExcludedPlaceData318.BadPlace c (t u v)) :
    (OriginalConstructedExcludedGenerators318.generators c u v hf j).generator b=
      frameScalar c (t u v) (hn c u v hf) i j*
        (OriginalConstructedExcludedGenerators318.generators c u v hf i).generator b := by
  change a0 c (t u v) (hn c u v hf) j / _ =
    frameScalar c (t u v) (hn c u v hf) i j*(a0 c (t u v) (hn c u v hf) i / _)
  rw [frameScalar_a0 c (t u v) (hn c u v hf) i j]
  ring

lemma excluded_norm_transition (b : OriginalExcludedPlaceData318.BadPlace c (t u v)) :
    OriginalExcludedPlaceData318.excludedNorm c (t u v) (hn c u v hf) j
      (OriginalConstructedExcludedGenerators318.generators c u v hf j) b=
    (b.val (frameScalar c (t u v) (hn c u v hf) i j))⁻¹*
      OriginalExcludedPlaceData318.excludedNorm c (t u v) (hn c u v hf) i
        (OriginalConstructedExcludedGenerators318.generators c u v hf i) b := by
  unfold OriginalExcludedPlaceData318.excludedNorm
  rw [excluded_generator_transition,map_mul,mul_inv_rev,mul_comm]

lemma finite_transition (w : FinitePlace (K c u v)) :
    (norms hλ hμ c u v hf j).finiteNorm w=
      (w (frameScalar c (t u v) (hn c u v hf) i j))⁻¹*
        (norms hλ hμ c u v hf i).finiteNorm w := by
  by_cases hw : w (ContactArithmeticDenominator318.denominator c:K c u v)=1
  · rw [good_finite hλ hμ c u v hf j w hw,good_finite hλ hμ c u v hf i w hw]
    exact OriginalGoodLatticeFrameChange318.norm_transition c (t u v) (hn c u v hf) w hw i j
  · change OriginalFiniteNormAssembly318.finiteNorm c (t u v) (hn c u v hf) j
      (OriginalConstructedExcludedGenerators318.generators c u v hf j) w=_
    change _ = (w (frameScalar c (t u v) (hn c u v hf) i j))⁻¹*
      OriginalFiniteNormAssembly318.finiteNorm c (t u v) (hn c u v hf) i
        (OriginalConstructedExcludedGenerators318.generators c u v hf i) w
    simp only [OriginalFiniteNormAssembly318.finiteNorm,dif_neg hw]
    exact excluded_norm_transition c u v hf i j ⟨w,hw⟩

lemma arch_transition (w : InfinitePlace (K c u v)) :
    (norms hλ hμ c u v hf j).arch w=
      (w (frameScalar c (t u v) (hn c u v hf) i j))⁻¹*
        (norms hλ hμ c u v hf i).arch w := by
  change OriginalArchimedeanFrameNorm318.frameNorm hλ hμ c (t u v) w j=_
  change _ = (w (frameScalar c (t u v) (hn c u v hf) i j))⁻¹*
    OriginalArchimedeanFrameNorm318.frameNorm hλ hμ c (t u v) w i
  rw [OriginalArchimedeanIntrinsicNorm318.frameNorm_transition hλ hμ c (t u v)
    (hn c u v hf) w i j]
  simp only [←mul_assoc,inv_mul_cancel₀ (w.pos (frameScalar_ne c (t u v)
    (hn c u v hf) i j)).ne',one_mul]

private lemma norms_ext {L : Type*} [Field L] [NumberField L]
    (F G : FrameNorms L) (ha : F.arch=G.arch) (hf : F.finiteNorm=G.finiteNorm) : F=G := by
  cases F
  cases G
  cases ha
  cases hf
  rfl

/-- The entire produced family, at EVERY finite and infinite place,
changes by the ORIGINAL rational frame scalar. Thus its normalized
adelic degree is intrinsic to these assembled local lattices. This
still does not identify them with a global regular-model Hodge/KS line. -/
theorem norms_rescale : norms hλ hμ c u v hf j=
    (norms hλ hμ c u v hf i).rescale
      (frameScalar c (t u v) (hn c u v hf) i j)⁻¹
      (inv_ne_zero (frameScalar_ne c (t u v) (hn c u v hf) i j)) := by
  apply norms_ext
  · funext w
    simpa only [FrameNorms.rescale,map_inv₀] using arch_transition hλ hμ c u v hf i j w
  · funext w
    simpa only [FrameNorms.rescale,map_inv₀] using finite_transition hλ hμ c u v hf i j w

theorem normalizedDegree_independent :
    (norms hλ hμ c u v hf j).normalizedDegree=
      (norms hλ hμ c u v hf i).normalizedDegree := by
  rw [norms_rescale hλ hμ c u v hf i j]
  exact FrameNorms.normalizedDegree_rescale _ _ _
end OriginalAllPlaceFrameCoherence318
