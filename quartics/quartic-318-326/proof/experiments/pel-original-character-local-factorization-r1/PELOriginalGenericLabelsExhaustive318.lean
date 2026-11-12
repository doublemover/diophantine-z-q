module
public import PELOriginalCharacterInvariantRing318
public import FourRootActualOrderAutomorphisms318
public section
noncomputable section
namespace PELOriginalGenericLabelsExhaustive318
open PELOriginalCommonContactBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterAffineImage318 PELOriginalActualCharacterFields318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩

@[expose] def originalAutomorphism (g:Labels):Raw≃ₐ[FourRootActualGenericField318.K]Raw:=
  FourRootActualGenericSigns318.genericAutomorphism branches (basis g)

/-- All automorphisms of the original degree16 field are accounted for by
actual original labels, not only an injective abstract group of order16. -/
theorem original_surjective:Function.Surjective originalAutomorphism:=by
  intro σ
  obtain ⟨s,hs⟩:=FourRootGalois318.signAutomorphism_surjective
    (FourRootActualGenericField318.parameter branches)
    ((AlgEquiv.autCongr (KummerTensorField318.rawEquiv
      (FourRootActualGenericField318.parameter branches))) σ)
  have he:FourRootAutomorphisms318.signEquiv
      (FourRootActualGenericField318.parameter branches) s=σ:=
    (AlgEquiv.autCongr (KummerTensorField318.rawEquiv
      (FourRootActualGenericField318.parameter branches))).injective hs
  let w:=FourRootInertiaLabelCardinality318.signEquivalence.symm s
  refine ⟨basis.symm w,?_⟩
  change FourRootAutomorphisms318.signEquiv
    (FourRootActualGenericField318.parameter branches)
    (FourBinaryCharacters318.signPattern (basis (basis.symm w)))=σ
  rw [basis.apply_symm_apply]
  have hw:FourBinaryCharacters318.signPattern w=s:=
    FourRootInertiaLabelCardinality318.signEquivalence.apply_symm_apply s
  rw [hw]
  exact he

/-- Exhaustion preserves the specified character kernel, rather than
relabeling the subgroup after comparing cardinalities. -/
theorem fixing_surjective (i:Fin 4) (σ:(field i).fixingSubgroup):
    ∃g:Labels,g∈(character i).ker ∧ originalAutomorphism g=σ.val:=by
  obtain ⟨g,hg⟩:=original_surjective σ.val
  refine ⟨g,?_,hg⟩
  apply (PELOriginalActualCharacterFields318.original_kernel i g).mp
  change originalAutomorphism g∈(field i).fixingSubgroup
  rw [hg]
  exact σ.property
end PELOriginalGenericLabelsExhaustive318
