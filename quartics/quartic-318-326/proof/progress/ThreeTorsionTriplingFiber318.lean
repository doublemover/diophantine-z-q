module
public import ThreeTorsionCompletedTripling318
public section
noncomputable section
namespace ThreeTorsionTriplingFiber318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The actual inverse image of the zero section under the constructed tripling composite. -/
@[expose] def fiber : Scheme :=
  pullback (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)

/-- Canonical map from the already constructed full rank-eight scheme into
that actual Scheme fiber. No equality with the whole fiber is inferred. -/
@[expose] def toFiber : ThreeTorsionScheme318.scheme A B hD⟶fiber A B hD :=
  pullback.lift (ThreeTorsionCompletedDoubling318.inclusion A B hD)
    (ThreeTorsionScheme318.structureMap A B hD)
    (ThreeTorsionCompletedTripling318.inclusion_tripling A B hD)

@[reassoc] theorem toFiber_fst : toFiber A B hD ≫ pullback.fst _ _ =
    ThreeTorsionCompletedDoubling318.inclusion A B hD := by simp [toFiber]
@[reassoc] theorem toFiber_snd : toFiber A B hD ≫ pullback.snd _ _ =
    ThreeTorsionScheme318.structureMap A B hD := by simp [toFiber]

theorem toFiber_unique (f:ThreeTorsionScheme318.scheme A B hD⟶fiber A B hD)
    (h₁:f≫pullback.fst _ _=ThreeTorsionCompletedDoubling318.inclusion A B hD)
    (h₂:f≫pullback.snd _ _=ThreeTorsionScheme318.structureMap A B hD) :
    f=toFiber A B hD := by
  apply pullback.hom_ext <;> simp only [h₁,h₂,toFiber_fst,toFiber_snd]
end ThreeTorsionTriplingFiber318
