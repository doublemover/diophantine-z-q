module
public import FourRootProjectiveDifferential318
public import FourRootActualRelativeCotangent318
public section
noncomputable section
namespace FourRootProjectiveDifferentialCharts318
open AlgebraicGeometry CategoryTheory Opposite Polynomial
open FourRootGluedScheme318 FourRootProjectiveProjection318
open FourRootIntrinsicCanonicalFrames318 FourRootProjectiveDifferential318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
@[expose] def finiteMap(i:Fin 4):Polynomial ℂ→ₐ[ℂ]FiniteRing b i:=
  Polynomial.aeval (FourRootActualBranchKaehler318.sourceParameter b i)
@[expose] def infinityMap:Polynomial ℂ→ₐ[ℂ]InfinityRing b hb:=
  Polynomial.aeval (FourRootActualInfinityKaehler318.reciprocalParameter b hb)
lemma finite_square(i:Fin 4):finiteEmbedding b i≫projection b=
    Spec.map (CommRingCat.ofHom (finiteMap b i).toRingHom)≫finiteBaseChart:=by
  rw [finiteEmbedding,Category.assoc,finite_projection,←Category.assoc,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,AlgHom.coe_toRingHom,finiteMap,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply ℂ (FourRootAffineCoordinateRing318.Ring b)
      (FiniteRing b i) c).symm
  · simp only [RingHom.comp_apply,AlgHom.coe_toRingHom,finiteMap,Polynomial.aeval_X]
    rfl
lemma infinity_square:infinityEmbedding b hb≫projection b=
    Spec.map (CommRingCat.ofHom (infinityMap b hb).toRingHom)≫infinityBaseChart b:=by
  rw [infinityEmbedding,Category.assoc,infinity_projection,←Category.assoc,←Category.assoc,
    ←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,AlgHom.coe_toRingHom,infinityMap,infinityCoordinate,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply ℂ (FourRootInfinityCoordinateRing318.Ring b)
      (InfinityRing b hb) c).symm
  · simp only [RingHom.comp_apply,AlgHom.coe_toRingHom,infinityMap,infinityCoordinate,Polynomial.aeval_X]
    rfl
lemma finite_preimage(i:Fin 4):finiteEmbedding b i ''ᵁ ⊤≤projection b ⁻¹ᵁ (finiteBaseChart ''ᵁ ⊤):=by
  rintro x ⟨q,_,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (finiteMap b i).toRingHom) q,trivial,?_⟩
  exact congrArg (fun f=>f q) (finite_square b i).symm
lemma infinity_preimage:infinityEmbedding b hb ''ᵁ ⊤≤projection b ⁻¹ᵁ (infinityBaseChart b ''ᵁ ⊤):=by
  rintro x ⟨q,_,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (infinityMap b hb).toRingHom) q,trivial,?_⟩
  exact congrArg (fun f=>f q) (infinity_square b hb).symm
@[expose] def finiteValue(i:Fin 4):Γ(baseOmega,finiteBaseChart ''ᵁ ⊤)→+
    Γ(omega b,finiteEmbedding b i ''ᵁ ⊤):=
  IntrinsicDifferentialSectionPullback318.value (projection b) (structureMap b) baseStructure
    (over_base b) _ _ (finite_preimage b i)
@[expose] def infinityValue:Γ(baseOmega,infinityBaseChart b ''ᵁ ⊤)→+
    Γ(omega b,infinityEmbedding b hb ''ᵁ ⊤):=
  IntrinsicDifferentialSectionPullback318.value (projection b) (structureMap b) baseStructure
    (over_base b) _ _ (infinity_preimage b hb)
/-- The actual derivative morphism sends the TRUE original finite base
frame dt to 2z_i times the true signed-root frame, on the whole actual
canonical chart. This pins the derivative, not just its support. -/
theorem finite_generator_image(i:Fin 4):finiteValue b i finiteBaseGenerator=
    ((finiteEmbedding b i).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
        (2*FourRootActualBranchKaehler318.sourceCoordinate b i)) • finiteGenerator b i:=by
  have h:=IntrinsicDifferentialSectionPullback318.sectionMap_naturality
    (projection b) (structureMap b) baseStructure (over_base b) (finiteMap b i)
    (finiteEmbedding b i) finiteBaseChart (finite_structure b i) finite_base_structure
    (finite_square b i) (finite_preimage b i)
  have he:=congrArg (fun f=>f (KaehlerDifferential.D ℂ (Polynomial ℂ) X)) h
  change finiteValue b i finiteBaseGenerator=IntrinsicChartSections318.sectionMap
    (finiteEmbedding b i) (structureMap b) (finite_structure b i)
    (AlgHomDifferential318.map (finiteMap b i) (KaehlerDifferential.D ℂ (Polynomial ℂ) X)) at he
  rw [AlgHomDifferential318.map_D,finiteMap,Polynomial.aeval_X,
    FourRootActualBranchKaehler318.parameter_differential,IntrinsicChartSections318.section_smul] at he
  exact he
/-- Infinity uses the SAME original projective map in its genuine
translated target chart v=1/(t-b0). Thus dv maps to 2u du. This is NOT
the meromorphic dt coefficient -2u^-3, nor the wrong rank-eight u-base. -/
theorem infinity_generator_image:infinityValue b hb (infinityBaseGenerator b)=
    ((infinityEmbedding b hb).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityRing b hb))).inv
        (2*FourRootActualInfinityKaehler318.coordinate b hb)) • infinityGenerator b hb:=by
  have h:=IntrinsicDifferentialSectionPullback318.sectionMap_naturality
    (projection b) (structureMap b) baseStructure (over_base b) (infinityMap b hb)
    (infinityEmbedding b hb) (infinityBaseChart b) (infinity_structure b hb) (infinity_base_structure b)
    (infinity_square b hb) (infinity_preimage b hb)
  have he:=congrArg (fun f=>f (KaehlerDifferential.D ℂ (Polynomial ℂ) X)) h
  change infinityValue b hb (infinityBaseGenerator b)=IntrinsicChartSections318.sectionMap
    (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
    (AlgHomDifferential318.map (infinityMap b hb) (KaehlerDifferential.D ℂ (Polynomial ℂ) X)) at he
  rw [AlgHomDifferential318.map_D,infinityMap,Polynomial.aeval_X,
    FourRootActualInfinityKaehler318.reciprocal_differential,IntrinsicChartSections318.section_smul] at he
  exact he
end FourRootProjectiveDifferentialCharts318
