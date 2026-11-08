module
public import InfinityGlobalChart318
public section
noncomputable section
namespace InfinityGlobalScheme318
open CategoryTheory AlgebraicGeometry
open InfinityGlobalBase318 InfinityGlobalChart318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)

@[expose] def actualOpen : (ContactProjectiveModel318.coverMap c).normalization.affineOpens :=
  ⟨(ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ(baseOpen c ''ᵁ ⊤),by
    apply IsAffineOpen.preimage
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange (baseOpen c)⟩

@[expose] def chartIso : ReciprocalInfinityNormalization318.neighborhood c≅Spec (chartRing c) :=
  Scheme.Spec.mapIso (actualChartEquiv c).toCommRingCatIso.op

/-- The explicit infinity neighborhood is an actual open subscheme of the
constructed global normalization, not a detached parallel affine model. -/
@[expose] def chartEmbedding : ReciprocalInfinityNormalization318.neighborhood c⟶
    (ContactProjectiveModel318.coverMap c).normalization :=
  (chartIso c).hom≫(actualOpen c).2.fromSpec

instance chartEmbedding_open : IsOpenImmersion (chartEmbedding c) := by
  unfold chartEmbedding
  infer_instance

/-- Its image is exactly the global normalization above the specified
reciprocal-line open. -/
theorem chartEmbedding_range : (chartEmbedding c).opensRange=(actualOpen c).1 := by
  change ((chartIso c).hom≫(actualOpen c).2.fromSpec).opensRange=_
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (actualOpen c).2.opensRange_fromSpec
end InfinityGlobalScheme318
