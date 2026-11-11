module
public import OriginalSmallPoleResidues318
public import ActualSourceHOneCharacterProjectors318

public section
noncomputable section
namespace ActualSourceHOneResidueBasis318
open ActualSourceHOnePrincipalRepresentatives318 ActualSourceHOneSmallPoles318
open ActualSourceHOneRationalSpanning318 OriginalSmallPoleResidues318
open ActualSourceHOneCharacterAction318 ActualSourceHOneCharacterProjectors318
open SourceHOneCharacterIndices318 SourceHOneCharacterRepresentatives318
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Both entire original chart images have zero low residues, so the residue
functionals annihilate the actual, exact Mayer-Vietoris kernel. -/
theorem kernel_le_lowResidues : boundaryLinear.ker ≤ (lowResidues units).ker := by
  intro x hx
  obtain ⟨a,b,hab⟩ := (ActualSourceHOneCoordinates318.boundary_eq_zero_iff x).mp hx
  change SourceOpenFractionField318.orderToOpen units a -
    InfinityOverlapLocalization318.toOpen units b = x at hab
  change lowResidues units x = 0
  rw [← hab,map_sub,low_finite,low_infinity,sub_self]

/-- Five genuine rational residue functionals on the unchanged actual H1. -/
@[expose] def residueMap : HOne →ₗ[ℚ] (SmallIndex → ℚ) :=
  boundaryLinear.liftOfSurjective ActualSourceHOneCoordinates318.boundary_surjective
    ⟨lowResidues units,kernel_le_lowResidues⟩

theorem residueMap_boundary (x : ActualSourceHOneCoordinates318.OverlapRing) :
    residueMap (boundary x) = lowResidues units x := by
  change (boundaryLinear.liftOfSurjective _) ⟨_,kernel_le_lowResidues⟩ (boundaryLinear x) = _
  rw [LinearMap.equivOfSurjective_apply]

/-- The original five-coordinate spanning map is exactly the boundary of
these same five overlap representatives. -/
theorem boundary_fiveRepresentatives (q : SmallIndex → ℚ) :
    boundary (fiveRepresentatives units q) = fiveLinear q := by
  change boundary (∑ s, OriginalNegativePoleUniqueness318.poleTerm units (q s) s.val.2.val s.val.1) = _
  rw [map_sum] <;> rfl

/-- Exact Kronecker pairing: every original coordinate is recovered, with
no assumed independence or cohomological nonvanishing premise. -/
theorem residueMap_fiveLinear (q : SmallIndex → ℚ) : residueMap (fiveLinear q) = q := by
  rw [← boundary_fiveRepresentatives,residueMap_boundary,low_fiveRepresentatives]

theorem fiveLinear_injective : Function.Injective fiveLinear :=
  Function.LeftInverse.injective residueMap_fiveLinear

/-- Actual whole-source H1 has the five explicit rational coordinates, with
the constructed original-ring residue map as inverse. -/
@[expose] def equivalence : (SmallIndex → ℚ) ≃ₗ[ℚ] HOne :=
  LinearEquiv.ofBijective fiveLinear ⟨fiveLinear_injective,fiveLinear_surjective⟩

theorem equivalence_apply (q : SmallIndex → ℚ) : equivalence q = fiveLinear q := rfl

theorem equivalence_symm (y : HOne) : equivalence.symm y = residueMap y := by
  have h := residueMap_fiveLinear (equivalence.symm y)
  change residueMap (equivalence (equivalence.symm y)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The dimension-five conclusion is derived from explicit original residues
and actual whole-H1 spanning, not a curve label or a differential substitute. -/
theorem source_finrank_eq_five : Module.finrank ℚ HOne = 5 := by
  have h := equivalence.finrank_eq
  rw [Module.finrank_pi,smallIndex_card] at h
  exact h.symm

/-- The five earlier root-character projector images are now proved nonzero
in actual cohomology, rather than merely nonzero in the contact function field. -/
theorem character_coordinates_nonzero : CoordinatesNonzero := by
  intro i hzero
  let s := smallIndex i
  have he : (1 : ℚ) = 0 := by
    calc
      1 = lowResidues units (representative units i) s := by
        simpa only [s,representative,OriginalNegativePoleUniqueness318.poleTerm,map_one,one_mul,ite_true]
          using (low_small_pole units 1 s s).symm
      _ = residueMap (characterClass i) s := by rw [characterClass,residueMap_boundary]
      _ = 0 := by rw [hzero,map_zero] <;> rfl
  norm_num at he

/-- The named original four triple-root coordinates and full-root coordinate
now give an unconditional rational equivalence with the actual source H1. -/
@[expose] def namedCharacterEquivalence : (Index → ℚ) ≃ₗ[ℚ] HOne :=
  coordinateEquivalence character_coordinates_nonzero

end ActualSourceHOneResidueBasis318
