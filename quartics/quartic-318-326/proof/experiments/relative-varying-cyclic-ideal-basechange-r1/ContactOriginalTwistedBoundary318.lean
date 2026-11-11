module
public import ContactOriginalTwistedRestriction318
public import ContactOriginalShiftedBoundary318
public section
noncomputable section
namespace ContactOriginalTwistedBoundary318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
open ContactWholeOpenSectionRestriction318 ContactOriginalCohomologyCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c)) (d : ℤ)

/-- The ACTUAL restriction-difference image of the ORIGINAL tensor-twisted
line is exactly the shifted old Laurent boundary. Chart preimages are
provided by the original whole-chart untwisting isomorphisms. -/
lemma difference_iff (s : Γ((twist c L d).object,finiteOpen c ⊓ infinityOpen c)) :
    s ∈ (OriginalLineMayerVietorisQuotient318.difference (twist c L d)
      (finiteOpen c) (infinityOpen c)).range ↔
    ContactOriginalTwistedRestriction318.coordinates c L d s ∈ LaurentCechFinite318.boundary
      (LaurentPositiveTwistVanishing318.transition
        (ContactOriginalLaurentCoordinates318.transition c L) d) := by
  rw [ContactOriginalShiftedBoundary318.boundary_iff]
  constructor
  · rintro ⟨⟨a,b⟩,hab⟩
    refine ⟨(finiteSectionsEquiv c L).symm
      (ContactOriginalTwistedRestriction318.finiteSections c L d (finiteOpen c) le_rfl a),
      (infinitySectionsEquiv c L).symm
      (ContactOriginalTwistedRestriction318.infinitySections c L d (infinityOpen c) le_rfl b),?_⟩
    have he := congrArg (ContactOriginalTwistedRestriction318.coordinates c L d) hab
    change ContactOriginalTwistedRestriction318.coordinates c L d
      ((twist c L d).object.presheaf.map (homOfLE inf_le_left).op a -
        (twist c L d).object.presheaf.map (homOfLE inf_le_right).op b) = _ at he
    simpa only [map_sub,ContactOriginalTwistedRestriction318.finite_restriction,
      ContactOriginalTwistedRestriction318.infinity_restriction,finite_res,infinity_res,
      AddEquiv.symm_apply_apply] using he
  · rintro ⟨a,b,hab⟩
    let a' := (ContactOriginalTwistedRestriction318.finiteSections c L d (finiteOpen c) le_rfl).symm
      (finiteSectionsEquiv c L a)
    let b' := (ContactOriginalTwistedRestriction318.infinitySections c L d (infinityOpen c) le_rfl).symm
      (infinitySectionsEquiv c L b)
    refine ⟨(a',b'),?_⟩
    apply (ContactOriginalTwistedRestriction318.coordinates c L d).injective
    change ContactOriginalTwistedRestriction318.coordinates c L d
      ((twist c L d).object.presheaf.map (homOfLE inf_le_left).op a' -
        (twist c L d).object.presheaf.map (homOfLE inf_le_right).op b') = _
    simpa only [map_sub,ContactOriginalTwistedRestriction318.finite_restriction,
      ContactOriginalTwistedRestriction318.infinity_restriction,a',b',LinearEquiv.apply_symm_apply,
      finite_res,infinity_res,AddEquiv.symm_apply_apply] using hab
end ContactOriginalTwistedBoundary318
