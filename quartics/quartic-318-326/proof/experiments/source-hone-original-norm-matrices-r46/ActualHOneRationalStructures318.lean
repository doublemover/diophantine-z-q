module
public import CohomologyRationalScalar318
public import ActualQuotientHOne318
public import ContactIntrinsicDifferentials318

public section
noncomputable section
namespace ActualHOneRational318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open SheafCohomologyRetraction318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev sourceMap := ContactIntrinsicDifferentials318.structureMap units
abbrev characterMap (i : Fin 4) := WeierstrassGluing318.structureMap (publishedA i) (publishedB i)
abbrev fifthMap := WeierstrassGluing318.structureMap FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B

/-- Structural rational action, defined on the unchanged actual common-source H1 group. -/
@[expose,reducible] def sourceModule : Module ℚ (structureH (ContactGlobalSmooth318.Model units) 1) := CohomologyRationalScalar318.structureModule sourceMap 1
@[expose,reducible] def characterModule (i : Fin 4) : Module ℚ (structureH (CompletedCharacterSchemeMaps318.Target i) 1) :=
  CohomologyRationalScalar318.structureModule (characterMap i) 1
@[expose,reducible] def fifthModule : Module ℚ (structureH FifthCompletedGlobal318.Target 1) :=
  CohomologyRationalScalar318.structureModule fifthMap 1
@[expose,reducible] def characterPushedModule (i : Fin 4) : Module ℚ (pushedH (CompletedCharacterGlobal318.completedMap i) 1) :=
  CohomologyRationalScalar318.pushedModule sourceMap (CompletedCharacterGlobal318.completedMap i) 1
@[expose,reducible] def fifthPushedModule : Module ℚ (pushedH FifthCompletedGlobal318.map 1) :=
  CohomologyRationalScalar318.pushedModule sourceMap FifthCompletedGlobal318.map 1

local instance sourceScalarInstance : Module ℚ (structureH (ContactGlobalSmooth318.Model units) 1) := sourceModule

theorem source_smul (a : ℚ) (x : (structureH (ContactGlobalSmooth318.Model units) 1)) :
    a • x = Sheaf.H.map (StructureRationalScalar318.multiply sourceMap a) 1 x := rfl

theorem character_smul (i : Fin 4) (a : ℚ) (x : structureH (CompletedCharacterSchemeMaps318.Target i) 1) :
    letI := characterModule i
    a • x = Sheaf.H.map (StructureRationalScalar318.multiply (characterMap i) a) 1 x := rfl

theorem fifth_smul (a : ℚ) (x : structureH FifthCompletedGlobal318.Target 1) :
    letI := fifthModule
    a • x = Sheaf.H.map (StructureRationalScalar318.multiply fifthMap a) 1 x := rfl


end ActualHOneRational318
