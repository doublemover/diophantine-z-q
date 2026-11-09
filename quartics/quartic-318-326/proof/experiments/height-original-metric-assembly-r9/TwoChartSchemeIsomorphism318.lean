module
public import IntegralOriginalFullIntersection318
public section
noncomputable section
namespace TwoChartSchemeIsomorphism318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y A B : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X) (f : X ⟶ Y)
variable [IsOpenImmersion a] [IsOpenImmersion b]
variable [IsOpenImmersion (a ≫ f)] [IsOpenImmersion (b ≫ f)]

/-- A map covered by two actual open chart embeddings is open. -/
theorem isOpenMap (cover : ∀ x,(∃ q,a q=x) ∨ (∃ q,b q=x)) : IsOpenMap f := by
  intro U hU
  have he : f '' U = (a ≫ f) '' (a ⁻¹' U) ∪ (b ≫ f) '' (b ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨q,rfl⟩ | ⟨q,rfl⟩ := cover x
      · exact Or.inl ⟨q,hx,rfl⟩
      · exact Or.inr ⟨q,hx,rfl⟩
    · rintro (⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩)
      · exact ⟨a q,hq,rfl⟩
      · exact ⟨b q,hq,rfl⟩
  rw [he]
  exact ((a ≫ f).isOpenEmbedding.isOpenMap _
    (hU.preimage a.isOpenEmbedding.continuous)).union
      ((b ≫ f).isOpenEmbedding.isOpenMap _ (hU.preimage b.isOpenEmbedding.continuous))

/-- A genuine scheme isomorphism criterion: chartwise open immersions,
all-point coverage, bijectivity, and the actual induced stalk maps. This does
not replace a scheme isomorphism by a bare bijection of complex points. -/
theorem isIso (cover : ∀ x,(∃ q,a q=x) ∨ (∃ q,b q=x))
    (hi : Function.Injective f) (hs : Function.Surjective f) : IsIso f := by
  rw [AlgebraicGeometry.isIso_iff_isIso_stalkMap]
  constructor
  · convert_to IsIso (TopCat.isoOfHomeo
      (Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective f ⟨hi,hs⟩)
        f.continuous (isOpenMap a b f cover))).hom
    infer_instance
  · intro x
    obtain ⟨q,rfl⟩ | ⟨q,rfl⟩ := cover x
    · haveI : IsIso (f.stalkMap (a q) ≫ a.stalkMap q) := by
        rw [←Scheme.Hom.stalkMap_comp]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (a.stalkMap q)
    · haveI : IsIso (f.stalkMap (b q) ≫ b.stalkMap q) := by
        rw [←Scheme.Hom.stalkMap_comp]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (b.stalkMap q)
end TwoChartSchemeIsomorphism318
