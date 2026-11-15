module
public import PELOriginalGenericLabelsExhaustive318
public section
noncomputable section
namespace PELOriginalCharacterRegularInvariants318
open PELOriginalCommonContactBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterAffineImage318 PELOriginalActualCharacterFields318
open PELOriginalCharacterInvariantRing318 PELOriginalGenericLabelsExhaustive318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩

/-- Membership in the literal invariant subring is equivalent to being
fixed by ALL original analytic kernel labels on the whole finite source. -/
theorem member_iff_original_kernel (i:Fin 4) (x:Source):
    x∈invariantSubring i ↔ ∀g:Labels,g∈(character i).ker →
      FourRootCoordinateRingSigns318.finiteEnd branches (basis g) x=x:=by
  constructor
  · intro hx g hg
    exact fixed_by_original_kernel i ⟨x,hx⟩ g hg
  · intro hx
    apply (member_fixed_by_all i x).mpr
    intro σ hσ
    obtain ⟨g,hg,he⟩:=fixing_surjective i ⟨σ,hσ⟩
    rw [←he]
    change FourRootActualGenericSigns318.genericAutomorphism branches (basis g)
      (FourRootActualGenericField318.affineEmbedding branches x)=_
    rw [←FourRootActualGenericSigns318.affineEmbedding_equivariant,hx g hg]

/-- Actual regular functions, not just rational functions, descend to
the old ordered target iff they are fixed by the original kernel. -/
theorem old_coordinate_image_iff (i:Fin 4) (x:Source):
    x∈Set.range (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i) ↔
      ∀g:Labels,g∈(character i).ker →
        FourRootCoordinateRingSigns318.finiteEnd branches (basis g) x=x:=by
  rw [PELOriginalCharacterAffineImage318.range_iff]
  exact member_iff_original_kernel i x
end PELOriginalCharacterRegularInvariants318
