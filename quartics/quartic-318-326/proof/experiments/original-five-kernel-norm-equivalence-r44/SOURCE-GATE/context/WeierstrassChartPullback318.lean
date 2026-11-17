module
public import WeierstrassGluing318
public import GenericOpenPushout318
import all WeierstrassGluing318
import all Mathlib.CategoryTheory.Limits.HasLimits
public section
noncomputable section
namespace WeierstrassChartPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
/-- Equality of the two chart images comes from an actual overlap point. -/
theorem exists_overlap (A B:R) (x:ShortAffineScheme318.scheme A B) (y:InfinitySmooth318.scheme A B)
    (h:finiteChart A B x=infinityChart A B y) :
    ∃z:overlap A B, intoAffine A B z=x ∧ intoInfinity A B z=y :=
  GenericOpenPushout318.exists_overlap (intoAffine A B) (intoInfinity A B) x y h

/-- The literal principal overlap is the actual categorical intersection of
the finite and infinity charts in the completed Scheme. -/
theorem square (A B:R) :
    IsPullback (intoAffine A B) (intoInfinity A B) (finiteChart A B) (infinityChart A B) :=
  GenericOpenPushout318.square (intoAffine A B) (intoInfinity A B)

@[expose] def overlapIso (A B:R) : overlap A B ≅ pullback (finiteChart A B) (infinityChart A B) :=
  (square A B).isoPullback
@[expose] def lift {X:Scheme.{u}} (A B:R)
    (f:X ⟶ ShortAffineScheme318.scheme A B) (g:X ⟶ InfinitySmooth318.scheme A B)
    (h:f ≫ finiteChart A B=g ≫ infinityChart A B) : X ⟶ overlap A B :=
  (square A B).lift f g h
@[reassoc] theorem lift_finite {X:Scheme.{u}} (A B:R)
    (f:X ⟶ ShortAffineScheme318.scheme A B) (g:X ⟶ InfinitySmooth318.scheme A B)
    (h:f ≫ finiteChart A B=g ≫ infinityChart A B) :
    lift A B f g h ≫ intoAffine A B=f := (square A B).lift_fst f g h
@[reassoc] theorem lift_infinity {X:Scheme.{u}} (A B:R)
    (f:X ⟶ ShortAffineScheme318.scheme A B) (g:X ⟶ InfinitySmooth318.scheme A B)
    (h:f ≫ finiteChart A B=g ≫ infinityChart A B) :
    lift A B f g h ≫ intoInfinity A B=g := (square A B).lift_snd f g h
end WeierstrassChartPullback318
