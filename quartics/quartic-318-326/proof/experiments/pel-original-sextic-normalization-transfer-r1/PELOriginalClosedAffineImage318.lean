module
public import PELOriginalLevelThreeClosedEmbedding318
public section
noncomputable section
namespace PELOriginalClosedAffineImage318
open Set Topology QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelProjectiveMap318 PELOriginalAllLevelHolomorphicMap318
open PELOriginalPolarizationTransitions318 ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  topology (Label 3)

/-- The actual original affine theta image. Its source is precisely the
nonzero homogeneous-coordinate locus, not a compact surrogate affine source. -/
@[expose] def affineImage : Set (TargetModel 1) :=
  {w | ∃ z : ComplexVectors, value τ hτ 3 j z ≠ 0 ∧ ratioVector τ hτ 1 j z = w}

/-- Equality with the inverse image of the ORIGINAL closed projective
image under the actual global inverse affine chart. -/
theorem affineImage_eq_preimage : affineImage τ hτ j =
    (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).symm ⁻¹'
      PELOriginalLevelThreeClosedEmbedding318.image τ hτ := by
  let c := ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hc : coveringMap τ hτ 1 z ∈ c.source :=
      (mk_mem_domain (Label 3) j _ _).mpr hz
    refine ⟨projection (P τ) z,?_⟩
    rw [original_covering_square]
    exact (c.left_inv hc).symm
  · rintro ⟨q,hq⟩
    obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
    rw [original_covering_square] at hq
    have hc : coveringMap τ hτ 1 z ∈ c.source := by
      rw [hq]
      exact c.map_target (mem_univ w)
    have hz : value τ hτ 3 j z ≠ 0 := (mk_mem_domain (Label 3) j _ _).mp hc
    refine ⟨z,hz,?_⟩
    rw [←actual_ratio,hq]
    exact c.right_inv (mem_univ w)

/-- The original affine chart image is CLOSED in the full ambient
complex affine model. Compactness is used only on the genuine original
projective source; no false compactness of an affine open is assumed. -/
theorem affineImage_closed : IsClosed (affineImage τ hτ j) := by
  rw [affineImage_eq_preimage]
  apply (PELOriginalLevelThreeClosedEmbedding318.image_closed τ hτ).preimage
  exact continuousOn_univ.mp
    (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).continuousOn_invFun
end PELOriginalClosedAffineImage318
