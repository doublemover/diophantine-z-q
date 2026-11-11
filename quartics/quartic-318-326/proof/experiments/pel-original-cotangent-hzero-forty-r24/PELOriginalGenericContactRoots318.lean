module
public import PELOriginalCommonCubicFiberEquiv318
public section
noncomputable section
namespace PELOriginalGenericContactRoots318
open PELOriginalCommonContactBase318 PELOriginalRegularCharacterProduct318
open FourCharacterRootRecombination318

/-- Merely regroup four equations on the SAME t; no geometric choice. -/
@[expose] def packCubics (t:ℂ) :
    (∀i,PELOriginalCommonCubicFiberEquiv318.CubicFiber t i) ≃ CubicTuple branches t where
  toFun y:=⟨fun i=>(y i).val,fun i=>(y i).property⟩
  invFun y:=fun i=>⟨y.val i,y.property i⟩
  left_inv y:=by funext i;rfl
  right_inv y:=by cases y;rfl

/-- Actual full genus-five generic fiber, not the fiber product at a
ramified point. All four original character quotients are taken from ONE
original source point, transported to the common manuscript base, and
recombined into the four literal linear roots. -/
@[expose] def rootsEquiv (t:ℂ) (hD:denominator branches t≠0) :
    SourceFiber (basePoint t) ≃ RootTuple branches t:=
  (genericFiber t hD).trans
    ((Equiv.piCongrRight (fun i=>PELOriginalCommonCubicFiberEquiv318.equivalence t hD i)).trans
      ((packCubics t).trans (FourCharacterRootRecombination318.equivalence branches t hD)))

/-- Exact source formula consumed by analytic extension. The denominator
is nonzero precisely on this full generic base, not on branch fibers. -/
lemma roots_formula (t:ℂ) (hD:denominator branches t≠0)
    (x:SourceFiber (basePoint t)) (i:Fin 4) :
    (rootsEquiv t hD x).val i=
      triple (fun k=>PELOriginalCommonCubicCoordinate318.ordinate k
        (PELOriginalCharacterQuotient318.toCharacter k x.val)) i/denominator branches t:=rfl

lemma roots_square (t:ℂ) (hD:denominator branches t≠0)
    (x:SourceFiber (basePoint t)) (i:Fin 4) :
    ((rootsEquiv t hD x).val i)^2=t-branches i:=(rootsEquiv t hD x).property i

theorem all_actual_roots (t:ℂ) (hD:denominator branches t≠0)
    (z:Fin 4→ℂ) (hz:∀i,z i^2=t-branches i) :
    ∃!x:SourceFiber (basePoint t),∀i,(rootsEquiv t hD x).val i=z i := by
  let target:RootTuple branches t:=⟨z,hz⟩
  refine ⟨(rootsEquiv t hD).symm target,?_,?_⟩
  · intro i
    exact congrArg (fun v:RootTuple branches t=>v.val i) ((rootsEquiv t hD).apply_symm_apply target)
  · intro y hy
    apply (rootsEquiv t hD).injective
    rw [(rootsEquiv t hD).apply_symm_apply]
    exact Subtype.ext (funext hy)
end PELOriginalGenericContactRoots318
