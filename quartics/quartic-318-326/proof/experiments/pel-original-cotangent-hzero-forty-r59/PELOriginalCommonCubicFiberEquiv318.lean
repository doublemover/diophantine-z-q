module
public import PELOriginalCommonCubicFibers318
public section
noncomputable section
namespace PELOriginalCommonCubicFiberEquiv318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalRegularCharacterProduct318
open PELOriginalCommonContactBase318 PELOriginalCommonCubicCoordinate318
open PELOriginalRegularCoverPatches318

/-- Every cardinality-defined branch of an actual character quotient is
in the FULL original branch image, using the exhaustive old labels. -/
lemma character_branch_subset (i:Fin 4) :
    PELOriginalCharacterBranches318.CharacterBranchValues i ⊆
      PELStabilizerLocusInvariant318.branchImage := by
  intro q hq
  obtain ⟨j,hj,rfl⟩:=
    (PELOriginalDirectCharacterBranches318.branch_values_iff i q).mp hq
  exact (PELOriginalFiniteRamification318.displayed j).property

/-- Generic common base implies the OLD actual regular locus. No
regularity assumption is added to the character-fiber equivalence. -/
lemma fiber_regular (t:ℂ)
    (hD:FourCharacterRootRecombination318.denominator branches t≠0)
    (i:Fin 4) (x:CharacterFiber (basePoint t) i) : x.val∈Regular i := by
  apply (PELOriginalCompletedLegendreBijection318.regular_iff i x.val).mpr
  intro hb
  have hc:toMaximal i x.val∈PELOriginalCharacterBranches318.CharacterBranchValues i:=
    (PELOriginalFourBranchCoordinate318.actual_branch_values i _).mpr hb
  exact ((PELOriginalCommonContactBase318.regular_iff t).mpr hD)
    (x.property ▸ character_branch_subset i hc)

lemma fiber_base (t:ℂ) (i:Fin 4) (x:CharacterFiber (basePoint t) i) :
    PELOriginalManuscriptNormalization318.coordinate (toMaximal i x.val)=(t:OnePoint ℂ):=by
  rw [x.property,basePoint_value]

abbrev CubicFiber (t:ℂ) (i:Fin 4):=
  {y:ℂ // y^2=FourCharacterRootRecombination318.cubic branches t i}

@[expose] def ordinateMap (t:ℂ)
    (hD:FourCharacterRootRecombination318.denominator branches t≠0) (i:Fin 4) :
    CharacterFiber (basePoint t) i→CubicFiber t i:=fun x=>
  ⟨ordinate i x.val,ordinate_square i x.val (fiber_regular t hD i x) t (fiber_base t i x)⟩

lemma ordinateMap_injective (t:ℂ)
    (hD:FourCharacterRootRecombination318.denominator branches t≠0) (i:Fin 4) :
    Function.Injective (ordinateMap t hD i) := by
  intro x y h
  apply Subtype.ext
  exact PELOriginalCommonCubicFibers318.fiber_injective i t x.val y.val
    (fiber_regular t hD i x) (fiber_regular t hD i y)
    (fiber_base t i x) (fiber_base t i y) (congrArg Subtype.val h)

/-- Both roots occur on the same actual base fiber. Surjectivity uses one
actual source point and its LITERAL original deck toggle; no arbitrary
elliptic isomorphism or independently chosen point is inserted. -/
lemma ordinateMap_surjective (t:ℂ)
    (hD:FourCharacterRootRecombination318.denominator branches t≠0) (i:Fin 4) :
    Function.Surjective (ordinateMap t hD i) := by
  intro y
  obtain ⟨a,ha⟩:=PELOriginalMaximalQuotient318.projection_surjective (basePoint t)
  let x:CharacterFiber (basePoint t) i:=⟨toCharacter i a,ha⟩
  have hs:y.val^2=(ordinate i x.val)^2:=y.property.trans (ordinateMap t hD i x).property.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he|he
  · exact ⟨x,Subtype.ext he.symm⟩
  · have hp:toMaximal i (PELOriginalCharacterDeck318.deck i x.val)=basePoint t:=by
      apply (PELOriginalFourBranchCoordinate318.coordinate i).injective
      exact (PELOriginalCharacterDeck318.deck_projection i x.val).trans
        (congrArg (PELOriginalFourBranchCoordinate318.coordinate i) x.property)
    let z:CharacterFiber (basePoint t) i:=⟨PELOriginalCharacterDeck318.deck i x.val,hp⟩
    refine ⟨z,Subtype.ext ?_⟩
    change ordinate i (PELOriginalCharacterDeck318.deck i x.val)=y.val
    rw [PELOriginalCommonCubicFibers318.ordinate_deck i x.val (fiber_regular t hD i x)]
    exact he.symm

@[expose] def equivalence (t:ℂ)
    (hD:FourCharacterRootRecombination318.denominator branches t≠0) (i:Fin 4) :
    CharacterFiber (basePoint t) i≃CubicFiber t i:=
  Equiv.ofBijective (ordinateMap t hD i)
    ⟨ordinateMap_injective t hD i,ordinateMap_surjective t hD i⟩
end PELOriginalCommonCubicFiberEquiv318
