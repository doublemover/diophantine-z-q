module
public import ContactRelativeTwistedCoordinates318
public import OriginalModuleTwoOpenGluing318
public section
noncomputable section
namespace ContactRelativeGlobalSectionLifting318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeWholeOpenSections318 ContactRelativeGeometricTwist318
open ContactRelativeTwistedCoordinates318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

@[expose] def finiteGlobal : Γ((twist R c L d).object,⊤) →+ finiteSections R c L :=
  (finiteEquiv R c L).symm.toAddMonoidHom.comp
    ((finiteCoordinates R c L d (finiteOpen R c) le_rfl).toAddEquiv.toAddMonoidHom.comp
      ((twist R c L d).object.presheaf.map (homOfLE (show finiteOpen R c ≤ ⊤ from le_top)).op).hom)
@[expose] def infinityGlobal : Γ((twist R c L d).object,⊤) →+ infinitySections R c L :=
  (infinityEquiv R c L).symm.toAddMonoidHom.comp
    ((infinityCoordinates R c L d (infinityOpen R c) le_rfl).toAddEquiv.toAddMonoidHom.comp
      ((twist R c L d).object.presheaf.map (homOfLE (show infinityOpen R c ≤ ⊤ from le_top)).op).hom)

/-- The two coordinates of EVERY actual global section satisfy the exact
original twisted overlap equation, with the genuine reciprocal factor. -/
lemma global_relation (s : Γ((twist R c L d).object,⊤)) :
    finiteRestriction R c L (finiteGlobal R c L d s) =
      (LaurentPolynomial.T d : LaurentPolynomial R) •
        infinityRestriction R c L (infinityGlobal R c L d s) := by
  have h : (twist R c L d).object.presheaf.map (homOfLE inf_le_left).op
      ((twist R c L d).object.presheaf.map (homOfLE (show finiteOpen R c ≤ ⊤ from le_top)).op s) =
    (twist R c L d).object.presheaf.map (homOfLE inf_le_right).op
      ((twist R c L d).object.presheaf.map (homOfLE (show infinityOpen R c ≤ ⊤ from le_top)).op s) := by
    rw [← Functor.map_comp_apply,← Functor.map_comp_apply]
    rfl
  have hc := congrArg (coordinates R c L d) h
  rw [finite_restriction,infinity_restriction] at hc
  exact hc

/-- Exact compatible original whole-chart coordinates glue to a genuine
global section of the actual twisted sheaf, retaining both coordinates. -/
lemma exists_section (a : finiteSections R c L) (b : infinitySections R c L)
    (hab : finiteRestriction R c L a =
      (LaurentPolynomial.T d : LaurentPolynomial R) • infinityRestriction R c L b) :
    ∃ s : Γ((twist R c L d).object,⊤), finiteGlobal R c L d s = a ∧ infinityGlobal R c L d s = b := by
  let sa := (finiteCoordinates R c L d (finiteOpen R c) le_rfl).symm (finiteEquiv R c L a)
  let sb := (infinityCoordinates R c L d (infinityOpen R c) le_rfl).symm (infinityEquiv R c L b)
  have hs : (twist R c L d).object.presheaf.map (homOfLE inf_le_left).op sa =
      (twist R c L d).object.presheaf.map (homOfLE inf_le_right).op sb := by
    apply (coordinates R c L d).injective
    rw [finite_restriction,infinity_restriction]
    simpa only [sa,sb,LinearEquiv.apply_symm_apply,AddEquiv.symm_apply_apply] using hab
  obtain ⟨s,ha,hb⟩ := OriginalModuleTwoOpenGluing318.exists_gluing
    (twist R c L d).object (finiteOpen R c) (infinityOpen R c) (cover R c) sa sb hs
  refine ⟨s,?_,?_⟩
  · change (finiteEquiv R c L).symm (finiteCoordinates R c L d (finiteOpen R c) le_rfl _) = a
    rw [ha]
    simp only [sa,LinearEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
  · change (infinityEquiv R c L).symm (infinityCoordinates R c L d (infinityOpen R c) le_rfl _) = b
    rw [hb]
    simp only [sb,LinearEquiv.apply_symm_apply,AddEquiv.symm_apply_apply]
end ContactRelativeGlobalSectionLifting318
