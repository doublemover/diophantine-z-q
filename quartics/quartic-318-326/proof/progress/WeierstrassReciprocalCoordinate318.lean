module
public import WeierstrassOverlap318
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public section
noncomputable section
namespace WeierstrassReciprocalCoordinate318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type*} [CommRing R] (A B:R)
abbrev I:=InfinityChart318.Ring A B
/-- Unit at the actual infinity point, allowing the reciprocal x-coordinate
to extend regularly across that point. -/
@[expose] def denominator:I A B:=
  1-algebraMap R (I A B) A*InfinityChart318.x A B*InfinityChart318.z A B-
    algebraMap R (I A B) B*(InfinityChart318.z A B)^2

theorem denominator_identity:
    InfinityChart318.z A B*denominator A B=(InfinityChart318.x A B)^3:=by
  have h:=InfinityChart318.relation A B
  dsimp [denominator]
  linear_combination h

theorem denominator_one:
    denominator A B+InfinityChart318.z A B*
      (algebraMap R (I A B) A*InfinityChart318.x A B+
        algebraMap R (I A B) B*InfinityChart318.z A B)=1:=by
  dsimp [denominator]
  ring

/-- The existing overlap D(z) and the reciprocal neighborhood D(D) cover the
entire actual infinity chart, over every commutative base ring. -/
theorem basicOpen_cover:
    PrimeSpectrum.basicOpen (InfinityChart318.z A B)⊔PrimeSpectrum.basicOpen (denominator A B)=⊤:=by
  apply le_antisymm le_top
  intro p _
  change InfinityChart318.z A B∉p.asIdeal ∨ denominator A B∉p.asIdeal
  by_cases hz:InfinityChart318.z A B∈p.asIdeal
  · right
    intro hd
    have h1:(1:I A B)∈p.asIdeal:=by
      rw [←denominator_one A B]
      exact p.asIdeal.add_mem hd (p.asIdeal.mul_mem_right _ hz)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal h1 isUnit_one)
  · exact Or.inl hz

abbrev Near:=Localization.Away (denominator A B)
@[expose] def x:Near A B:=algebraMap (I A B) (Near A B) (InfinityChart318.x A B)
@[expose] def z:Near A B:=algebraMap (I A B) (Near A B) (InfinityChart318.z A B)
@[expose] def inverseD:Near A B:=IsLocalization.Away.invSelf (denominator A B)
@[expose] def reciprocal:Near A B:=(x A B)^2*inverseD A B

theorem local_relation:z A B=(x A B)^3*inverseD A B:=by
  have h:=congrArg (algebraMap (I A B) (Near A B)) (denominator_identity A B)
  simp only [map_mul,map_pow] at h
  change z A B*algebraMap (I A B) (Near A B) (denominator A B)=(x A B)^3 at h
  have hi:=IsLocalization.Away.mul_invSelf (S:=Near A B) (denominator A B)
  change algebraMap (I A B) (Near A B) (denominator A B)*inverseD A B=1 at hi
  calc
    z A B=z A B*(algebraMap (I A B) (Near A B) (denominator A B)*inverseD A B):=by rw [hi,mul_one]
    _=(x A B)^3*inverseD A B:=by rw [←mul_assoc,h]

abbrev Common:=Localization.Away (z A B)
@[expose] def forward:Common A B:=
  algebraMap (Near A B) (Common A B) (x A B)*IsLocalization.Away.invSelf (z A B)
@[expose] def inverse:Common A B:=
  algebraMap (Near A B) (Common A B) (reciprocal A B)

/-- On the whole actual common localization, affine x and its reciprocal
multiply to one. No cancellation at infinity or generic-point inference. -/
theorem forward_inverse:forward A B*inverse A B=1:=by
  have h:=congrArg (algebraMap (Near A B) (Common A B)) (local_relation A B)
  simp only [map_mul,map_pow] at h
  dsimp [forward,inverse,reciprocal]
  simp only [map_mul,map_pow]
  calc
    _=(algebraMap (Near A B) (Common A B) (x A B)^3*
      algebraMap (Near A B) (Common A B) (inverseD A B))*IsLocalization.Away.invSelf (z A B):=by ring
    _=algebraMap (Near A B) (Common A B) (z A B)*IsLocalization.Away.invSelf (z A B):=by rw [←h]
    _=1:=IsLocalization.Away.mul_invSelf _
end WeierstrassReciprocalCoordinate318
