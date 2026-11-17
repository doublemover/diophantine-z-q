module
public import PELOriginalWholeCharacterFinite318
public section
noncomputable section
namespace PELOriginalOrderedCharacterFraction318
open PELOriginalCommonContactBase318 PELOriginalActualCharacterFields318
open FourRootActualGenericField318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent (parameter branches)):=
  ⟨independent branches branches_injective⟩
abbrev Order (i:Fin 4):=PELOriginalOrderedCharacterCoordinates318.Target i
abbrev Character (i:Fin 4):=PELOriginalActualCharacterFields318.field i
abbrev Raw:=FourRootActualFractionField318.L branches

/-- The actual ordered affine ring embeds into the OLD original
character subfield using the SAME ordered coordinate equivalence. -/
@[expose] def embedding (i:Fin 4):Order i→+*Character i:=
  (FourRootCharacterPolynomialOrder318.embedding branches branches_injective
    (omitted i) (omitted_nonempty i)).comp
      (PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i).symm.toRingHom
lemma embedding_injective (i:Fin 4):Function.Injective (embedding i):=
  (FourRootCharacterPolynomialOrder318.embedding_injective branches branches_injective
    (omitted i) (omitted_nonempty i)).comp
      (PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i).symm.injective
local instance cubicAlgebra (i:Fin 4):Algebra (PELOriginalWholeCharacterOrders318.Cubic i) (Character i):=
  (FourRootCharacterPolynomialOrder318.embedding branches branches_injective
    (omitted i) (omitted_nonempty i)).toAlgebra
local instance orderAlgebra (i:Fin 4):Algebra (Order i) (Character i):=(embedding i).toAlgebra

/-- The entire specified character field, not a fresh abstract quadratic
field, is the fraction field of the exact target affine order. -/
theorem actual_fractionField (i:Fin 4):IsFractionRing (Order i) (Character i):=by
  letI:=PELOriginalWholeCharacterOrders318.fraction_field i
  exact IsFractionRing.of_ringEquiv_left
    (PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i).symm.toRingEquiv (fun x=>rfl)

/-- The coordinate embedding agrees with the old whole affine character
map INSIDE the original full field, including the specified scale/sign. -/
lemma embedding_square (i:Fin 4) (x:Order i):
    affineEmbedding branches (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i x)=
      (embedding i x:Raw):=by
  exact FourRootCharacterWholeAffineMap318.embedding_square branches branches_injective
    (omitted i) (omitted_nonempty i)
    ((PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i).symm x)
end PELOriginalOrderedCharacterFraction318
