module
public import ActualTwoDescentOriginalOverlapInclusionIsomorphism318
public section
noncomputable section
namespace ActualTwoDescentFullOverlapMapRestriction318
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y Z W : Scheme.{u}} (j : Y ⟶ X) (k : Z ⟶ X) (l : W ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]

/-- Invertibility on a full overlap controls the actual pushed map on
EVERY subopen of the other chart, with no top-section-only inference. -/
lemma actual_push_restrict_isIso {M N : Y.Modules} (f : M ⟶ N)
    (hr : j⁻¹ᵁ k.opensRange=l.opensRange)
    [IsIso ((Scheme.Modules.restrictFunctor l).map f)] :
    IsIso ((Scheme.Modules.restrictFunctor k).map ((Scheme.Modules.pushforward j).map f)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let V := j⁻¹ᵁ(k ''ᵁ U)
  have hv : V ≤ l.opensRange := by
    rw [←hr,←Scheme.Hom.image_top_eq_opensRange]
    exact j.preimage_mono (k.image_mono le_top)
  have he : l ''ᵁ (l⁻¹ᵁ V)=V := by
    apply SetLike.coe_injective
    exact Set.image_preimage_eq_iff.mpr hv
  have hi := (Scheme.Modules.Hom.isIso_iff_isIso_app.mp
    (inferInstance : IsIso ((Scheme.Modules.restrictFunctor l).map f))) (l⁻¹ᵁ V)
  have hb := (ConcreteCategory.isIso_iff_bijective _).mp hi
  change Function.Bijective (f.app (l ''ᵁ (l⁻¹ᵁ V))) at hb
  rw [he] at hb
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hb
end ActualTwoDescentFullOverlapMapRestriction318
