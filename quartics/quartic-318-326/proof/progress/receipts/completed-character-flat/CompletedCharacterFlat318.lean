module
public import CompletedCharacterFinite318
public import CompletedRationalDedekind318
public import DedekindAffineFlat318
public section
noncomputable section
namespace CompletedCharacterFlat318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral:IsIntegral (ContactProjectiveModel318.model units):=
  ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i

/-- Flatness of the actual completed character morphism, on the entire
source and target including all finite branch points and infinity. -/
theorem completedMap_flat (i:Fin 4):Flat (completedMap i):=by
  have hD:IsUnit (-16*(4*(publishedA i)^3+27*(publishedB i)^2)):=
    isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (published_nonsingular i))
  letI:=CompletedRationalDedekind318.affine (publishedA i) (publishedB i) hD
  letI:=CompletedRationalDedekind318.infinity (publishedA i) (publishedB i) hD
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P:=@Flat)
  intro p
  rcases WeierstrassGluing318.charts_cover (publishedA i) (publishedB i) p with h|h
  · let U:=(WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat (completedMap i)
      (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
  · let U:=(WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat (completedMap i)
      (CommRingCat.of (InfinityChart318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))

/-- Finite, flat and surjective refer to exactly the already constructed
whole completedMap, not a generic field inclusion or a replacement model. -/
theorem finite_flat_surjective (i:Fin 4):
    IsFinite (completedMap i) ∧ Flat (completedMap i) ∧ Surjective (completedMap i):=
  ⟨CompletedCharacterFinite318.completedMap_finite i,completedMap_flat i,
    CompletedCharacterProper318.completedMap_surjective i⟩
end CompletedCharacterFlat318
