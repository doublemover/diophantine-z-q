module
public import PELOriginalUniversalParallelogram318
public import PELOriginalPolarizationTheoremOfSquare318
public section
noncomputable section
namespace PELOriginalPolarizationParallelogram318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalProductChartCover318 PELOriginalParallelogramCover318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def pulledLine (t : Fin 4) (L : Line (candidate τ hτ)) : Line (Product τ hτ) :=
  LineSheafPullback318.line (maps τ hτ t) L
abbrev pull (t : Fin 4) := LineClassPullbackGroup318.hom (maps τ hτ t)

lemma cubic_class :
    pull τ hτ 2 (classOf (cubicLine τ hτ))*pull τ hτ 3 (classOf (cubicLine τ hτ))=
      (pull τ hτ 0 (classOf (cubicLine τ hτ))*pull τ hτ 1 (classOf (cubicLine τ hτ)))^2 := by
  have he : classOf (LineSheafTensor318.line (pulledLine τ hτ 2 (cubicLine τ hτ))
      (pulledLine τ hτ 3 (cubicLine τ hτ)))=
    classOf (LineSheafTensorPower318.line (LineSheafTensor318.line
      (pulledLine τ hτ 0 (cubicLine τ hτ)) (pulledLine τ hτ 1 (cubicLine τ hτ))) 2) :=
    classOf_eq (PELOriginalUniversalParallelogram318.iso τ hτ 3
      (PELOriginalUniversalHyperplaneInputs318.cubic τ hτ))
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power,
    LineSheafClassGroup318.classOf_tensor] at he
  exact he

lemma quadratic_class :
    pull τ hτ 2 (classOf (quadraticLine τ hτ))*pull τ hτ 3 (classOf (quadraticLine τ hτ))=
      (pull τ hτ 0 (classOf (quadraticLine τ hτ))*pull τ hτ 1 (classOf (quadraticLine τ hτ)))^2 := by
  have he : classOf (LineSheafTensor318.line (pulledLine τ hτ 2 (quadraticLine τ hτ))
      (pulledLine τ hτ 3 (quadraticLine τ hτ)))=
    classOf (LineSheafTensorPower318.line (LineSheafTensor318.line
      (pulledLine τ hτ 0 (quadraticLine τ hτ)) (pulledLine τ hτ 1 (quadraticLine τ hτ))) 2) :=
    classOf_eq (PELOriginalUniversalParallelogram318.iso τ hτ 2
      (PELOriginalUniversalHyperplaneInputs318.quadratic τ hτ))
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power,
    LineSheafClassGroup318.classOf_tensor] at he
  exact he

/-- Universal parallelogram for the SAME algebraic degree-one line,
on the ENTIRE actual product scheme. Both hyperplane identities are
whole sheaf isomorphisms, not unrelated pointwise normalizations. -/
theorem class_formula :
    pull τ hτ 2 (classOf (line τ hτ))*pull τ hτ 3 (classOf (line τ hτ))=
      (pull τ hτ 0 (classOf (line τ hτ))*pull τ hτ 1 (classOf (line τ hτ)))^2 := by
  rw [PELOriginalPolarizationCube318.class_difference]
  simp only [map_mul,map_inv]
  calc
    _ = (pull τ hτ 2 (classOf (cubicLine τ hτ))*pull τ hτ 3 (classOf (cubicLine τ hτ)))*
        (pull τ hτ 2 (classOf (quadraticLine τ hτ))*pull τ hτ 3 (classOf (quadraticLine τ hτ)))⁻¹ := by group
    _ = _ := by rw [cubic_class,quadratic_class]; group

@[expose] def sourceLine : Line (Product τ hτ) :=
  LineSheafTensor318.line (pulledLine τ hτ 2 (line τ hτ)) (pulledLine τ hτ 3 (line τ hτ))
@[expose] def targetLine : Line (Product τ hτ) :=
  LineSheafTensorPower318.line
    (LineSheafTensor318.line (pulledLine τ hτ 0 (line τ hτ)) (pulledLine τ hτ 1 (line τ hτ))) 2

/-- Actual m*L tensor d*L isomorphism to the square of pr1*L tensor
pr2*L, on the whole product. A normalization along axes is not asserted. -/
@[expose] def iso : (sourceLine τ hτ).object ≅ (targetLine τ hτ).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [sourceLine,targetLine,LineSheafClassGroup318.classOf_tensor,
    LineSheafTensorPower318.classOf_power,LineSheafClassGroup318.classOf_tensor]
  exact class_formula τ hτ

/-- The produced WHOLE product isomorphism pulls back along any actual
test morphism, including nonreduced schemes. This is stronger than a
separate choice of an isomorphism at each complex parameter. -/
@[expose] def testIso {T : Scheme} (f : T ⟶ Product τ hτ) :
    (Scheme.Modules.pullback f).obj (sourceLine τ hτ).object ≅
      (Scheme.Modules.pullback f).obj (targetLine τ hτ).object :=
  (Scheme.Modules.pullback f).mapIso (iso τ hτ)
lemma test_hom_inv {T : Scheme} (f : T ⟶ Product τ hτ) :
    (testIso τ hτ f).hom≫(testIso τ hτ f).inv=𝟙 _ := (testIso τ hτ f).hom_inv_id
end PELOriginalPolarizationParallelogram318
