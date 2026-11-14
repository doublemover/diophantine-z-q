module
public import PELOriginalCommonCubicCoordinate318
public section
noncomputable section
namespace PELOriginalCommonCubicFibers318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalManuscriptNormalization318
open PELOriginalGluedLegendreMap318 PELOriginalRegularCoverPatches318
open PELOriginalCommonCubicCoordinate318 PELOriginalOrderedMatrixTransport318
open PELOriginalCompletedLegendreBijection318

/-- Equality of the new ordinate on one actual original base fiber
recovers BOTH old coordinates and hence the original source point. -/
theorem fiber_injective (i:Fin 4) (t:ℂ) (x y:CharacterBase i)
    (hx:x∈Regular i) (hy:y∈Regular i)
    (hxt:coordinate (toMaximal i x)=(t:OnePoint ℂ))
    (hyt:coordinate (toMaximal i y)=(t:OnePoint ℂ))
    (h:PELOriginalCommonCubicCoordinate318.ordinate i x=
      PELOriginalCommonCubicCoordinate318.ordinate i y) : x=y := by
  have hbase:toMaximal i x=toMaximal i y:=coordinate.injective (hxt.trans hyt.symm)
  have hz:(coordinates i x).1=(coordinates i y).1:=by
    apply OnePoint.coe_injective
    rw [coordinates_projection i x hx,coordinates_projection i y hy]
    exact congrArg (PELOriginalFourBranchCoordinate318.coordinate i) hbase
  have hw:(coordinates i x).2=(coordinates i y).2:=by
    rw [ordinate_formula,ordinate_formula,←hz] at h
    exact mul_left_cancel₀ (coefficient_ne i x hx t hxt) h
  have hf:finiteMap i ⟨x,hx⟩=finiteMap i ⟨y,hy⟩:=
    Subtype.ext (Prod.ext hz hw)
  exact congrArg Subtype.val (PELOriginalGluedLegendreFibers318.finiteMap_injective i hf)

lemma deck_regular (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    PELOriginalCharacterDeck318.deck i x∈Regular i := by
  rw [regular_iff,PELOriginalCharacterDeck318.deck_projection]
  exact (regular_iff i x).mp hx

/-- The old finite coordinates intertwine the literal original toggle
and actual y-negation, by the already constructed completed comparison. -/
lemma coordinates_deck (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    coordinates i (PELOriginalCharacterDeck318.deck i x)=
      ((coordinates i x).1,-(coordinates i x).2) := by
  have h:=PELOriginalCharacterDeck318.completedMap_equivariant i x
  rw [completedMap_regular i ⟨_,deck_regular i x hx⟩,
    completedMap_regular i ⟨x,hx⟩] at h
  have hh:finiteMap i ⟨_,deck_regular i x hx⟩=
      NormalizedLegendreFieldPoints318.sign
        (PELOriginalFourBranchCoordinate318.branchParameter i) (finiteMap i ⟨x,hx⟩):=
    Option.some.inj h
  exact congrArg Subtype.val hh

/-- Sign equivariance is about the ORIGINAL character deck, not a deck
operation invented by transport from the common cubic. -/
theorem ordinate_deck (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    PELOriginalCommonCubicCoordinate318.ordinate i (PELOriginalCharacterDeck318.deck i x)=
      -PELOriginalCommonCubicCoordinate318.ordinate i x := by
  unfold PELOriginalCommonCubicCoordinate318.ordinate
  rw [coordinates_deck i x hx]
  change scale i*PELOriginalOrderedMatrixTransport318.ordinate i
    (coordinates i x).1 (-(coordinates i x).2)=_
  rw [ordinate_sign,mul_neg]
end PELOriginalCommonCubicFibers318
