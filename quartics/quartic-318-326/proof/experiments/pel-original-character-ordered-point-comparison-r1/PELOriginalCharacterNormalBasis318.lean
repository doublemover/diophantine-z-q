module
public import PELOriginalCharacterNormalOpens318
public import NormalAffineBasis318
public section
noncomputable section
namespace PELOriginalCharacterNormalBasis318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterNormalOpens318
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2

/-- The normal affine basis is constructed on the SAME original target,
from its actual finite and infinity chart images and section isomorphisms. -/
theorem hasBasis (i:Fin 4):NormalAffineBasis318.HasBasis (Curve i):=by
  let V:Bool→(Curve i).Opens:=fun b=>if b then infinityOpen i else finiteOpen i
  apply NormalAffineBasis318.of_cover (Curve i) V
  · intro p
    rcases PELOriginalCharacterNormalOpens318.covers i p with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · intro b
    cases b
    · exact finite_affine i
    · exact infinity_affine i
  · intro b
    cases b
    · exact finite_normal i
    · exact infinity_normal i
end PELOriginalCharacterNormalBasis318
