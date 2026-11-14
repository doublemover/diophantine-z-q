module
public import ActualOpenIdealInclusion318
public section
noncomputable section
namespace ActualOpenIdealRange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X W Y : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (q : W ⟶ Y) (k : W ⟶ Z) (j : Y ⟶ X) [IsOpenImmersion j]
  (hs : IsPullback q k j p) (V : Y.affineOpens)
local notation "M" => ActualClosedIdealModule318.object p
local notation "V'" => (⟨j ''ᵁ V.1,V.2.image_of_isOpenImmersion j⟩ : X.affineOpens)

/-- On every ORIGINAL affine open of an open Cartesian base change, the
restricted actual ideal inclusion has exactly the new closed ideal. -/
lemma range_eq : LinearMap.range ((ActualOpenIdealInclusion318.hom p j).val.app (op V.1)).hom=
    q.ker.ideal V := by
  rw [ker_ideal_of_isPullback_of_isOpenImmersion p q k j hs V]
  ext a
  constructor
  · rintro ⟨s,rfl⟩
    change (j.appIso V.1).inv ((ActualOpenIdealInclusion318.hom p j).app V.1 s)∈p.ker.ideal V'
    rw [ActualOpenIdealInclusion318.formula,Iso.hom_inv_id_apply]
    rw [← ActualClosedIdealRange318.range_ideal p V']
    exact ⟨(M.restrictAppIso j V.1).hom s,rfl⟩
  · intro ha
    change (j.appIso V.1).inv a∈p.ker.ideal V' at ha
    rw [← ActualClosedIdealRange318.range_ideal p V'] at ha
    obtain ⟨s,hs⟩ := ha
    refine ⟨(M.restrictAppIso j V.1).inv s,?_⟩
    rw [ActualOpenIdealInclusion318.formula,Iso.inv_hom_id_apply,hs,Iso.inv_hom_id_apply]
end ActualOpenIdealRange318
