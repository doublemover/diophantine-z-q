module
public import FixedCoordinateFrameFunctor318
public section
noncomputable section
namespace NegatedCoordinateFrameFunctor318
open KaehlerDifferential
universe u v
variable {R:Type u} {S:Type v} [CommRing R] [CommRing S] [Algebra R S]
    (e:KaehlerDifferential R S≃ₗ[S]S) (t:S) (het:e (D R S t)=1)
    (f:S→ₐ[R]S) (hft:f t= -t)
include het hft
/-- A genuine du frame acquires the derivative sign when the coordinate
is negated. The coefficient action remains the actual semilinear ring map. -/
theorem map_frame (ω:KaehlerDifferential R S):
    e (AlgHomDifferential318.map f ω)= -f (e ω):=by
  have he:ω=e ω • D R S t:=by
    apply e.injective
    rw [map_smul,het,smul_eq_mul,mul_one]
  calc
    e (AlgHomDifferential318.map f ω)=
      e (AlgHomDifferential318.map f (e ω • D R S t)):=congrArg (fun v=>e (AlgHomDifferential318.map f v)) he
    _= -f (e ω):=by
      simp only [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,hft,
        map_neg,map_smul,het,smul_eq_mul,mul_neg,mul_one]
theorem fixed_coefficient (ω:KaehlerDifferential R S)
    (h:AlgHomDifferential318.map f ω=ω):f (e ω)= -e ω:=by
  have hh:(-f (e ω))=e ω:=(map_frame e t het f hft ω).symm.trans (congrArg e h)
  exact neg_eq_iff_eq_neg.mp hh
end NegatedCoordinateFrameFunctor318
