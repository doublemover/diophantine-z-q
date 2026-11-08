module
public import LiteralIndependentFrameChange318
public section
noncomputable section
namespace LiteralIndependentFrameAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 (Points)
open LiteralKernelAddition318 F3FrameChange318
open LiteralIndependentPairOpen318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
/-- The original two actual universal points over the represented open. -/
@[expose] def frame : Fin 2→Points N (inclusion N ≫ productBase N):=fun i=>
  LiteralKernelFunctor318.precomposeLinear N (productBase N) (inclusion N)
    (LiteralKernelFrameChange318.frame N i)
@[reassoc] theorem first (g:Group) :
    LiteralIndependentFrameChange318.map N g ≫ LiteralIndependentPairFunctor318.first N=
    (change g (frame N) 0).val:=by
  rw [LiteralIndependentPairFunctor318.first,←Category.assoc,
    LiteralIndependentFrameChange318.map_inclusion,Category.assoc,LiteralKernelFrameChange318.map_fst]
  unfold frame
  simpa only [LiteralKernelFunctor318.precomposeLinear_value] using congrArg Subtype.val
    (change_natural (LiteralKernelFunctor318.precomposeLinear N (productBase N) (inclusion N))
      g (LiteralKernelFrameChange318.frame N) 0)
@[reassoc] theorem second (g:Group) :
    LiteralIndependentFrameChange318.map N g ≫ LiteralIndependentPairFunctor318.second N=
    (change g (frame N) 1).val:=by
  rw [LiteralIndependentPairFunctor318.second,←Category.assoc,
    LiteralIndependentFrameChange318.map_inclusion,Category.assoc,LiteralKernelFrameChange318.map_snd]
  unfold frame
  simpa only [LiteralKernelFunctor318.precomposeLinear_value] using congrArg Subtype.val
    (change_natural (LiteralKernelFunctor318.precomposeLinear N (productBase N) (inclusion N))
      g (LiteralKernelFrameChange318.frame N) 1)
variable {X:Scheme}
/-- Actual right action on every Scheme test, including nonreduced and
nonaffine tests, defined by postcomposition with the checked Scheme maps. -/
@[expose] def action (g:Group) (f:X ⟶ scheme N) : X ⟶ scheme N:=
  f ≫ LiteralIndependentFrameChange318.map N g
@[simp] theorem action_one (f:X ⟶ scheme N) : action N 1 f=f:=by
  simp only [action,LiteralIndependentFrameChange318.map_one,Category.comp_id]
theorem action_mul (g h:Group) (f:X ⟶ scheme N) :
    action N h (action N g f)=action N (g*h) f:=by
  simp only [action,Category.assoc,LiteralIndependentFrameChange318.map_mul]
theorem natural {Y:Scheme} (k:Y ⟶ X) (g:Group) (f:X ⟶ scheme N) :
    action N g (k ≫ f)=k ≫ action N g f:=Category.assoc _ _ _
/-- Exact two-section transformation on an arbitrary Scheme test. -/
@[expose] def testFrame (f:X ⟶ scheme N) : Fin 2→Points N (f ≫ (inclusion N ≫ productBase N)):=
  fun i=>LiteralKernelFunctor318.precomposeLinear N (inclusion N ≫ productBase N) f (frame N i)
theorem action_first (g:Group) (f:X ⟶ scheme N) :
    action N g f ≫ LiteralIndependentPairFunctor318.first N=(change g (testFrame N f) 0).val:=by
  rw [action,Category.assoc,first]
  unfold testFrame
  simpa only [LiteralKernelFunctor318.precomposeLinear_value] using congrArg Subtype.val
    (change_natural (LiteralKernelFunctor318.precomposeLinear N (inclusion N ≫ productBase N) f)
      g (frame N) 0)
theorem action_second (g:Group) (f:X ⟶ scheme N) :
    action N g f ≫ LiteralIndependentPairFunctor318.second N=(change g (testFrame N f) 1).val:=by
  rw [action,Category.assoc,second]
  unfold testFrame
  simpa only [LiteralKernelFunctor318.precomposeLinear_value] using congrArg Subtype.val
    (change_natural (LiteralKernelFunctor318.precomposeLinear N (inclusion N ≫ productBase N) f)
      g (frame N) 1)
end LiteralIndependentFrameAction318
