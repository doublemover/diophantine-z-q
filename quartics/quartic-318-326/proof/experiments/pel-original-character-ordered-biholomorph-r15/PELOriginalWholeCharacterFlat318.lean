module
public import PELOriginalWholeCharacterFinite318
public import FieldWeierstrassDedekind318
public import DedekindAffineFlat318
public section
noncomputable section
namespace PELOriginalWholeCharacterFlat318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral:IsIntegral (FourRootGluedScheme318.scheme branches):=
  FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=
  PELOriginalWholeCharacterFinite318.finite i
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=
  PELOriginalWholeCharacterProper318.dominant i

/-- Flatness of the actual completed character morphism, on the entire
source and target including all finite branch points and infinity. -/
theorem flat (i:Fin 4):Flat (morphism i):=by
  have hD:IsUnit (-16*(4*(A i)^3+27*(B i)^2)):=
    isUnit_iff_ne_zero.mpr (NormalizedLegendreProjectiveModel318.discriminant_ne
      (PELOriginalOrderedCharacterCoordinate318.parameter i)
      (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).1
      (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).2)
  letI:=FieldWeierstrassDedekind318.affine (A i) (B i) hD
  letI:=FieldWeierstrassDedekind318.infinity (A i) (B i) hD
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P:=@Flat)
  intro p
  rcases WeierstrassGluing318.charts_cover (A i) (B i) p with h|h
  · let U:=(WeierstrassGluing318.finiteChart (A i) (B i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat (morphism i)
      (CommRingCat.of (ShortAffineJacobian318.Ring (A i) (B i)))
      (WeierstrassGluing318.finiteChart (A i) (B i))
  · let U:=(WeierstrassGluing318.infinityChart (A i) (B i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat (morphism i)
      (CommRingCat.of (InfinityChart318.Ring (A i) (B i)))
      (WeierstrassGluing318.infinityChart (A i) (B i))

/-- Finite, flat and surjective refer to exactly the already constructed
whole completedMap, not a generic field inclusion or a replacement model. -/
theorem finite_flat_surjective (i:Fin 4):
    IsFinite (morphism i) ∧ Flat (morphism i) ∧ Surjective (morphism i):=
  ⟨PELOriginalWholeCharacterFinite318.finite i,flat i,
    PELOriginalWholeCharacterProper318.surjective i⟩
end PELOriginalWholeCharacterFlat318
