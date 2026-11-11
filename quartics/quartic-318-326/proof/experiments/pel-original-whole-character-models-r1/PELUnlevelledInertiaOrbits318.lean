module
public import PELOriginalInertiaOrbitSeparation318
public section
noncomputable section
namespace PELUnlevelledInertiaOrbits318
open QuaternionicJointPeriodTopology318 PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELInertiaArithmeticFixedPoints318 PELOriginalInertiaOrbitSeparation318
open PELNormOneBaseAction318 PELEffectiveNormOneAction318 PELUnlevelledComplexBase318
set_option maxHeartbeats 1500000

/-- The five original points remain in DISTINCT orbits even after the
full positive original-order normalizer acts and norm-one level is forgotten.
No assertion of branch completeness or prescribed cross-ratios is made. -/
theorem index_of_unlevelled_normalizer_orbit (g : positiveNormalizer) (i j : Fin 5)
    (h : projection (baseAction g (originalFixedPoint i))=projection (originalFixedPoint j)) : i=j := by
  obtain ⟨v,hv⟩ := covering.apply_eq_iff_mem_orbit.mp h
  obtain ⟨u,hu⟩ := effectiveMap_surjective v
  have he : baseAction (originalNormalizer u) (originalFixedPoint j)=
      baseAction g (originalFixedPoint i) := by
    rw [←hu] at hv
    exact hv
  apply index_of_upstairs_orbit ((originalNormalizer u)⁻¹*g) i j
  rw [baseAction_mul,←he,←baseAction_mul,inv_mul_cancel,baseAction_one]

theorem original_points_injective :
    Function.Injective (fun i : Fin 5 => projection (originalFixedPoint i)) := by
  intro i j h
  apply index_of_unlevelled_normalizer_orbit 1 i j
  simpa only [baseAction_one] using h
end PELUnlevelledInertiaOrbits318
