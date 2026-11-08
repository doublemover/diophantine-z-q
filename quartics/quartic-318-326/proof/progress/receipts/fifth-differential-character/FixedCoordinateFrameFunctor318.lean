module
public import AlgHomDifferential318
public section
noncomputable section
namespace FixedCoordinateFrameFunctor318
open KaehlerDifferential
universe u v
variable {R:Type u} {S:Type v} [CommRing R] [CommRing S] [Algebra R S]
    (e:KaehlerDifferential R S≃ₗ[S]S) (t:S) (het:e (D R S t)=1)
    (f:S→ₐ[R]S) (hft:f t=t)
include het hft
/-- A genuine dt frame intertwines differential pullback with the actual
ring map whenever that map fixes the specified coordinate. -/
theorem map_frame (ω:KaehlerDifferential R S):
    e (AlgHomDifferential318.map f ω)=f (e ω):=by
  have he:ω=e ω • D R S t:=by
    apply e.injective
    rw [map_smul,het,smul_eq_mul,mul_one]
  calc
    e (AlgHomDifferential318.map f ω)=
      e (AlgHomDifferential318.map f (e ω • D R S t)):=congrArg (fun v=>e (AlgHomDifferential318.map f v)) he
    _=f (e ω):=by
      rw [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,hft,
        map_smul,het,smul_eq_mul,mul_one]
end FixedCoordinateFrameFunctor318
