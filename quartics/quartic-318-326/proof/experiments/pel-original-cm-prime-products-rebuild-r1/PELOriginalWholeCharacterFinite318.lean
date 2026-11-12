module
public import PELOriginalCharacterBaseProjection318
public import ProperFiniteFiberDescent318
public section
noncomputable section
namespace PELOriginalWholeCharacterFinite318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterBaseProjection318

lemma target_separated (i:Fin 4):IsSeparated (targetTMap i):=by
  haveI:IsSeparated (targetTMap i≫ProjectiveJLine318.structureMap ℂ):=by
    rw [target_over_complex]
    exact NormalizedLegendreProjectiveModel318.separated _
  exact IsSeparated.of_comp (targetTMap i) (ProjectiveJLine318.structureMap ℂ)

/-- Actual global finiteness follows from the exact original finite
projective projection and the separated target t-map. No target-fiber
cardinality, quotient universal property, or generic rank is assumed. -/
theorem finite (i:Fin 4):IsFinite (morphism i):=by
  letI:=target_separated i
  haveI:IsFinite (morphism i≫targetTMap i):=by
    rw [full_composite]
    exact FourRootActualProperModel318.projection_finite branches
  exact IsFinite.of_comp (morphism i) (targetTMap i)

lemma target_proper (i:Fin 4):IsProper (targetTMap i):=by
  haveI:IsProper (targetTMap i≫ProjectiveJLine318.structureMap ℂ):=by
    rw [target_over_complex]
    exact NormalizedLegendreProjectiveModel318.proper _
  exact IsProper.of_comp (targetTMap i) (ProjectiveJLine318.structureMap ℂ)

/-- The same independent Legendre model is itself finite over the
original t-line. Full fibers are finite images of the original projection
fibers under the proved global surjective character morphism. -/
theorem target_finite (i:Fin 4):IsFinite (targetTMap i):=by
  letI:=target_proper i
  letI:=PELOriginalWholeCharacterProper318.surjective i
  haveI:IsFinite (morphism i≫targetTMap i):=by
    rw [full_composite]
    exact FourRootActualProperModel318.projection_finite branches
  exact ProperFiniteFiberDescent318.finite (morphism i) (targetTMap i) (morphism i).surjective

theorem finite_surjective (i:Fin 4):IsFinite (morphism i) ∧ Surjective (morphism i):=
  ⟨finite i,PELOriginalWholeCharacterProper318.surjective i⟩
end PELOriginalWholeCharacterFinite318
