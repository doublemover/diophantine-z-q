module
public import PELOriginalUniversalCube318
public import PELOriginalPolarizationCube318
public section
noncomputable section
namespace PELOriginalPolarizationCubeIdentity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalTripleProductReduced318 PELOriginalCubeSchemeMaps318 PELOriginalCubeLineFrames318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def pulledLine (t : Fin 11) (L : Line (candidate τ hτ)) : Line (Triple τ hτ) :=
  LineSheafPullback318.line (maps τ hτ t) L
abbrev pull (t : Fin 11) := LineClassPullbackGroup318.hom (maps τ hτ t)
@[expose] def fourLine (side : Bool) (L : Line (candidate τ hτ)) : Line (Triple τ hτ) :=
  LineSheafTensor318.line
    (LineSheafTensor318.line
      (LineSheafTensor318.line (pulledLine τ hτ (positions side 0) L)
        (pulledLine τ hτ (positions side 1) L))
      (pulledLine τ hτ (positions side 2) L))
    (pulledLine τ hτ (positions side 3) L)
@[expose] def expression (side : Bool) (c : Class (candidate τ hτ)) : Class (Triple τ hτ) :=
  pull τ hτ (positions side 0) c*pull τ hτ (positions side 1) c*
    pull τ hτ (positions side 2) c*pull τ hτ (positions side 3) c
lemma fourLine_class (side : Bool) (L : Line (candidate τ hτ)) :
    classOf (fourLine τ hτ side L)=expression τ hτ side (classOf L) := by
  simp only [fourLine,LineSheafClassGroup318.classOf_tensor]
  rfl
lemma cubic_class : expression τ hτ true (classOf (cubicLine τ hτ))=
    expression τ hτ false (classOf (cubicLine τ hτ)) := by
  have h : classOf (fourLine τ hτ true (cubicLine τ hτ))=
      classOf (fourLine τ hτ false (cubicLine τ hτ)) :=
    classOf_eq (PELOriginalUniversalCube318.iso τ hτ 3 (PELOriginalCubeBasisCoefficients318.cubic τ hτ))
  simpa only [fourLine_class] using h
lemma quadratic_class : expression τ hτ true (classOf (quadraticLine τ hτ))=
    expression τ hτ false (classOf (quadraticLine τ hτ)) := by
  have h : classOf (fourLine τ hτ true (quadraticLine τ hτ))=
      classOf (fourLine τ hτ false (quadraticLine τ hτ)) :=
    classOf_eq (PELOriginalUniversalCube318.iso τ hτ 2 (PELOriginalCubeBasisCoefficients318.quadratic τ hτ))
  simpa only [fourLine_class] using h
lemma expression_mul (side : Bool) (a b : Class (candidate τ hτ)) :
    expression τ hτ side (a*b)=expression τ hτ side a*expression τ hτ side b := by
  simp only [expression,map_mul]
  group
lemma expression_inv (side : Bool) (a : Class (candidate τ hτ)) :
    expression τ hτ side a⁻¹=(expression τ hτ side a)⁻¹ := by
  simp only [expression,map_inv]
  group

/-- Genuine theorem of cube for the SAME degree-one algebraic line,
on the WHOLE original triple scheme. The zero-map line factor is explicit. -/
theorem class_formula : expression τ hτ true (classOf (line τ hτ))=
    expression τ hτ false (classOf (line τ hτ)) := by
  rw [PELOriginalPolarizationCube318.class_difference]
  simp only [expression_mul,expression_inv]
  rw [cubic_class,quadratic_class]
@[expose] def iso : (fourLine τ hτ true (line τ hτ)).object ≅
    (fourLine τ hτ false (line τ hτ)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [fourLine_class,fourLine_class]
  exact class_formula τ hτ

/-- Every scheme test inherits the actual cube identity, including
nonreduced tests. No comparison solely on closed fibers is used. -/
@[expose] def testIso {T : Scheme} (f : T ⟶ Triple τ hτ) :
    (Scheme.Modules.pullback f).obj (fourLine τ hτ true (line τ hτ)).object ≅
      (Scheme.Modules.pullback f).obj (fourLine τ hτ false (line τ hτ)).object :=
  (Scheme.Modules.pullback f).mapIso (iso τ hτ)
lemma test_hom_inv {T : Scheme} (f : T ⟶ Triple τ hτ) :
    (testIso τ hτ f).hom≫(testIso τ hτ f).inv=𝟙 _ := (testIso τ hτ f).hom_inv_id
lemma test_inv_hom {T : Scheme} (f : T ⟶ Triple τ hτ) :
    (testIso τ hτ f).inv≫(testIso τ hτ f).hom=𝟙 _ := (testIso τ hτ f).inv_hom_id
end PELOriginalPolarizationCubeIdentity318
