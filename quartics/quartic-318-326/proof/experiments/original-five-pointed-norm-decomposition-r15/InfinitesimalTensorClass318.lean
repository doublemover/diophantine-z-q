module
public import AdditiveCocycleSum318
public import CocycleTensorIso318
public section
noncomputable section
namespace InfinitesimalTensorClass318
open AlgebraicGeometry CategoryTheory InfinitesimalUnitCocycle318 LineSheafClass318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (e : Γ(X,⊤)) (he : e * e = 0) (hc : (⊤ : X.Opens) ≤ ⨆ i, U i)
lemma cocycle_add (c d : AdditiveCocycle X U) :
    cocycle X e he U (AdditiveCocycleSum318.add U c d) =
      UnitCocycleProduct318.product (cocycle X e he U c) (cocycle X e he U d) := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact infinitesimal_add _ _ _ _
/-- The tensor product is the ORIGINAL module-sheaf tensor. Its genuine frames
and transition multiplication identify it with the line of the sum cocycle. -/
@[expose] def tensorIso (c d : AdditiveCocycle X U) :
    (LineSheafTensor318.line (line X e he U c hc) (line X e he U d hc)).object ≅
      (line X e he U (AdditiveCocycleSum318.add U c d) hc).object :=
  CocycleTensorIso318.iso U (cocycle X e he U c) (cocycle X e he U d) hc ≪≫
    eqToIso (congrArg (CocycleModule318.object U) (cocycle_add X U e he c d).symm)
lemma class_add (c d : AdditiveCocycle X U) :
    classOf (line X e he U (AdditiveCocycleSum318.add U c d) hc) =
      classOf (line X e he U c hc) * classOf (line X e he U d hc) :=
  classOf_eq (tensorIso X U e he hc c d).symm
end InfinitesimalTensorClass318
