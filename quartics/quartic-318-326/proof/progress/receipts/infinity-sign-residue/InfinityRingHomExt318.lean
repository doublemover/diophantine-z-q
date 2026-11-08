module
public import InfinitySignCoordinates318
public section
noncomputable section
namespace InfinityRingHomExt318
open Polynomial InfinityReciprocalAction318 InfinityOrderCoordinates318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type*} [CommRing F] [Algebra ℚ F]
/-- Whole-ring extensionality retains both the ramified coordinate and
all three actual unit-root generators, including the localized denominator. -/
theorem hom_ext {f g:Order c→+*F}
    (hu:f (coordinate c)=g (coordinate c))
    (hr:∀j:Fin 3,f (generator c j)=g (generator c j)):f=g:=by
  apply ThreeRootCoordinates318.ringHom_ext (coefficient c) ?_ hr
  apply IsLocalization.ringHom_ext (Submonoid.powers (InfinityOpenChart318.denominator c))
  apply Polynomial.ringHom_ext
  · intro q
    change f (algebraMap ℚ (Order c) q)=g (algebraMap ℚ (Order c) q)
    rw [RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap]
  · exact hu
end InfinityRingHomExt318
