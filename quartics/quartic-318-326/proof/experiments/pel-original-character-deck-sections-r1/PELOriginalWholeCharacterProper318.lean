module
public import PELOriginalWholeCharacterMorphisms318
public import FourRootActualProperModel318
public import CompletedIntegral318
public section
noncomputable section
namespace PELOriginalWholeCharacterProper318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Properness uses the actual original source proper model and the
same target separated structure appearing in the structure square. -/
theorem proper (i:Fin 4):IsProper (morphism i):=by
  letI:=NormalizedLegendreProjectiveModel318.separated
    (PELOriginalOrderedCharacterCoordinate318.parameter i)
  letI:IsProper (morphism i≫WeierstrassGluing318.structureMap (A i) (B i)):=by
    rw [over_complex]
    exact FourRootActualProperModel318.proper branches
  exact IsProper.of_comp (morphism i) (WeierstrassGluing318.structureMap (A i) (B i))

/-- Integral lying-over for the OLD exact finite character ring map. -/
lemma finite_chart_surjective (i:Fin 4):
    Function.Surjective (PELOriginalOrderedCharacterSchemeMaps318.morphism i):=
  (PELOriginalOrderedCharacterSchemeMaps318.finite_ring i).to_isIntegral.comap_surjective
    (PELOriginalOrderedCharacterSchemeMaps318.injective i)

/-- Surjectivity on the whole finite chart gives dominance in the actual
integral proper target, not dominance of a merely related affine model. -/
theorem dominant (i:Fin 4):IsDominant (morphism i):=by
  letI:Surjective (PELOriginalOrderedCharacterSchemeMaps318.morphism i):=⟨finite_chart_surjective i⟩
  letI:=CompletedIntegral318.completed_irreducible (A i) (B i)
  letI:=AffineCoordinateDomain318.affine_domain (A i) (B i)
  letI:Nonempty (ShortAffineScheme318.scheme (A i) (B i)):=by
    change Nonempty (Spec (CommRingCat.of (ShortAffineJacobian318.Ring (A i) (B i))))
    infer_instance
  letI:IsDominant (WeierstrassGluing318.finiteChart (A i) (B i)):=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (WeierstrassGluing318.finiteChart (A i) (B i)).isOpenEmbedding.isOpenMap⟩
  letI:IsDominant (FourRootGluedScheme318.finiteChart branches≫morphism i):=by
    rw [on_finite,finiteMap]
    infer_instance
  exact IsDominant.of_comp (FourRootGluedScheme318.finiteChart branches) (morphism i)

theorem surjective (i:Fin 4):Surjective (morphism i):=by
  letI:=proper i
  letI:=dominant i
  infer_instance

theorem target_smooth (i:Fin 4):Smooth (WeierstrassGluing318.structureMap (A i) (B i)):=
  NormalizedLegendreProjectiveModel318.smooth
    (PELOriginalOrderedCharacterCoordinate318.parameter i)
    (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).1
    (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).2

theorem target_proper_integral (i:Fin 4):
    IsProper (WeierstrassGluing318.structureMap (A i) (B i)) ∧ IsIntegral (Curve i):=
  ⟨NormalizedLegendreProjectiveModel318.proper _,CompletedIntegral318.completed_integral _ _⟩
end PELOriginalWholeCharacterProper318
