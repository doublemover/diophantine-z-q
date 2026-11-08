module
public import FifthCompletedFinite318
public import CompletedRationalDedekind318
public import DedekindAffineFlat318
public section
noncomputable section
namespace FifthCompletedFlat318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral (ContactGlobalSmooth318.Model units):=
  ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
/-- Flatness on both entire target charts, including the chosen elliptic zero
and every finite branch value, for the unchanged actual fifth quotient map. -/
theorem flat:Flat map:=by
  letI:=CompletedRationalDedekind318.affine A B discriminant_unit
  letI:=CompletedRationalDedekind318.infinity A B discriminant_unit
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P:=@Flat)
  intro p
  rcases WeierstrassGluing318.charts_cover A B p with h|h
  · let U:=(WeierstrassGluing318.finiteChart A B).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat map
      (CommRingCat.of (ShortAffineJacobian318.Ring A B)) (WeierstrassGluing318.finiteChart A B)
  · let U:=(WeierstrassGluing318.infinityChart A B).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact DedekindAffineFlat318.restrict_chart_flat map
      (CommRingCat.of (InfinityChart318.Ring A B)) (WeierstrassGluing318.infinityChart A B)
theorem finite_flat_surjective:IsFinite map∧Flat map∧Surjective map:=
  ⟨FifthCompletedFinite318.finite,flat,FifthCompletedProper318.surjective⟩
end FifthCompletedFlat318
