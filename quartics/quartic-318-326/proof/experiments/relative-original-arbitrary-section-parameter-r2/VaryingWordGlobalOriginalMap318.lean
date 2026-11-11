module
public import VaryingWordParameterStructure318
public section
noncomputable section
namespace VaryingWordGlobalOriginalMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "N" w => VaryingNormalizedWordParameter318.ring R A ι w
local notation "H" w v => VaryingNormalizedWordOverlap318.ring R A ι w v
local notation "F" w v => VaryingWordOverlapFamily318.frame R A ι w v
local notation "inc" => VaryingWordOverlapFamily318.into R A ι
local notation "t" => VaryingWordFamilyTransition318.transition R A ι
local notation "p" => VaryingNormalizedUniversalFamily318.projection R A ι
local notation "z" => VaryingWordFamilyGluing318.into R A ι
abbrev chart (w : ι → List A) : VaryingNormalizedUniversalFamily318.family R A ι w ⟶ Spec (CommRingCat.of A) :=
  VaryingNormalizedUniversalFamily318.intoSource R A ι w ≫
    VaryingSourceCoefficientPullback318.original R A (N w)
abbrev overlap (w v : ι → List A) : VaryingWordOverlapFamily318.scheme R A ι w v ⟶ Spec (CommRingCat.of A) :=
  CyclicQuotientFiniteFlat318.into (F w v).action (F w v).marked ≫
    VaryingSourceCoefficientPullback318.original R A (H w v)
@[reassoc] lemma inclusion_original (w v : ι → List A) : inc w v ≫ chart R A ι w=overlap R A ι w v := by
  have h : inc w v ≫ VaryingNormalizedUniversalFamily318.intoSource R A ι w=
      CyclicQuotientFiniteFlat318.into (F w v).action (F w v).marked ≫
        VaryingSourceCoefficientPullback318.sourceChange R A (N w) (H w v)
          (VaryingNormalizedWordOverlap318.inclusion R A ι w v) :=
    (VaryingNormalizedFamilyBaseChange318.cartesian R A ι w (N w) (H w v)
      (VaryingNormalizedWordOverlap318.inclusion R A ι w v)
      (VaryingNormalizedWordOverlap318.universal R A ι w)).w.symm
  have h' := congrArg (fun k => k ≫ VaryingSourceCoefficientPullback318.original R A (N w)) h
  simpa only [chart,overlap,Category.assoc,VaryingSourceCoefficientPullback318.source_original] using h'
@[reassoc] lemma transition_original (w v : ι → List A) :
    (t w v).hom ≫ overlap R A ι v w=overlap R A ι w v := by
  change Spec.map (CommRingCat.ofHom (VaryingWordFamilyTransition318.ringEquiv R A ι w v).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (VaryingWordOverlapFamily318.ideal R A ι v w))) ≫
      VaryingSourceCoefficientPullback318.original R A (H v w))=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (VaryingWordOverlapFamily318.ideal R A ι w v))) ≫
      VaryingSourceCoefficientPullback318.original R A (H w v)
  simp only [VaryingSourceCoefficientPullback318.original,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change VaryingWordFamilyTransition318.ringEquiv R A ι w v
      (Ideal.Quotient.mk (VaryingWordOverlapFamily318.ideal R A ι v w) ((1 : H v w) ⊗ₜ[R] a))=
    Ideal.Quotient.mk (VaryingWordOverlapFamily318.ideal R A ι w v) ((1 : H w v) ⊗ₜ[R] a)
  rw [VaryingWordFamilyTransition318.ringEquiv_mk]
  simp only [VaryingWordFamilyTransition318.sourceEquiv,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,map_one,AlgEquiv.refl_apply]

/-- The global family maps to the ORIGINAL source affine scheme, with
all original source elements fixed by the regular frame transitions. -/
@[expose] def original : VaryingWordFamilyGluing318.scheme R A ι ⟶ Spec (CommRingCat.of A) := by
  fapply Multicoequalizer.desc
  · exact chart R A ι
  rintro ⟨w,v⟩
  change inc w v ≫ chart R A ι w=((t w v).hom ≫ inc v w) ≫ chart R A ι v
  simp only [Category.assoc,inclusion_original,transition_original]
@[reassoc] lemma into_original (w : ι → List A) : z w ≫ original R A ι=chart R A ι w :=
  Multicoequalizer.π_desc _ _ _ _ _

lemma chart_structure (w : ι → List A) :
    chart R A ι w ≫ VaryingSourceCoefficientPullback318.base R A=
      p w ≫ VaryingWordParameterStructure318.chart R A ι w := by
  have h := congrArg (fun k => VaryingNormalizedUniversalFamily318.intoSource R A ι w ≫ k)
    (VaryingSourceCoefficientPullback318.tensor_cartesian R A (N w)).w.symm
  have hp := VaryingQuotientCoefficientPullback318.into_projection R A ι w (N w)
    (VaryingNormalizedWordOverlap318.universal R A ι w)
  simpa only [chart,← Category.assoc,hp] using h

/-- Both global maps have the SAME original coefficient-ring structure. -/
lemma structure_square : original R A ι ≫ VaryingSourceCoefficientPullback318.base R A=
    VaryingWordGlobalFamilyProjection318.projection R A ι ≫
      VaryingWordParameterStructure318.structureMap R A ι := by
  apply Scheme.Cover.hom_ext (VaryingWordFamilyGluing318.cover R A ι) _ _
  intro w
  change z w ≫ (original R A ι ≫ _)=z w ≫
    (VaryingWordGlobalFamilyProjection318.projection R A ι ≫ _)
  rw [← Category.assoc,into_original,← Category.assoc,
    VaryingWordGlobalFamilyProjection318.into_projection,Category.assoc,
    VaryingWordParameterStructure318.into_structureMap]
  exact chart_structure R A ι w
end VaryingWordGlobalOriginalMap318
