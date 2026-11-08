module
public import ThreeTorsionTriplingFiber318
public import ThreeTorsionClosed318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace ThreeTorsionCompletedClosed318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ThreeTorsionCompletedDoubling318 ThreeTorsionTriplingFiber318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The entire actual torsion algebra gives a closed subscheme of the completed curve,
not merely a map whose geometric points lie there. -/
theorem inclusion_closed : IsClosedImmersion (inclusion A B hD) := by
  letI := ThreeTorsionClosed318.inclusion_closed A B hD
  haveI : Mono (inclusion A B hD) := by unfold inclusion; infer_instance
  letI := CubicClosedImmersion318.structure_separated A B
  haveI : IsFinite (inclusion A B hD ≫ WeierstrassGluing318.structureMap A B) := by
    rw [inclusion_over_base]
    exact (ThreeTorsionScheme318.finite_etale A B hD).1
  haveI : IsFinite (inclusion A B hD) :=
    IsFinite.of_comp (inclusion A B hD) (WeierstrassGluing318.structureMap A B)
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance,inferInstance⟩

/-- The canonical factor into the actual tripling zero-fiber is a closed immersion.
This does not identify it with the whole fiber or its nonzero component. -/
theorem toFiber_closed : IsClosedImmersion (toFiber A B hD) := by
  let π := pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)
  letI := inclusion_closed A B hD
  haveI : Mono (toFiber A B hD) := by
    constructor
    intro X f g he
    apply (cancel_mono (inclusion A B hD)).mp
    have hh := congrArg (fun k => k ≫ π) he
    simpa only [π,Category.assoc,toFiber_fst] using hh
  letI := CubicClosedImmersion318.infinity_closed A B
  haveI : IsClosedImmersion π := by dsimp only [π]; infer_instance
  haveI : IsFinite (toFiber A B hD ≫ π) := by
    change IsFinite (toFiber A B hD ≫ pullback.fst _ _)
    rw [toFiber_fst]
    infer_instance
  haveI : IsFinite (toFiber A B hD) := IsFinite.of_comp (toFiber A B hD) π
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance,inferInstance⟩
end ThreeTorsionCompletedClosed318
