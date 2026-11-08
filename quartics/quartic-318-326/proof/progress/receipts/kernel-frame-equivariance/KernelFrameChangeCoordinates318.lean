module
public import F3FrameCoefficients318
public import LiteralIndependentSectionAction318
public import KernelUniversalFrame318
public section
noncomputable section
namespace KernelFrameChangeCoordinates318
open AlgebraicGeometry CategoryTheory
open F3FrameChange318 KernelUniversalFrame318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
lemma frame_eq : LiteralIndependentFrameAction318.frame N=![first N,second N]:=by
  funext i
  apply Subtype.ext
  fin_cases i <;> rfl
@[expose] def pull (g:F3FrameChange318.Group) :=
  restrict N (LiteralIndependentFrameChange318.map N g) (frameBase N)
    (LiteralIndependentSectionAction318.map_structure N g)
lemma pull_first (g:F3FrameChange318.Group) : pull N g (first N)=change g ![first N,second N] 0:=by
  apply Subtype.ext
  rw [show pull N g (first N)=restrict N (LiteralIndependentFrameChange318.map N g) (frameBase N)
    (LiteralIndependentSectionAction318.map_structure N g) (first N) from rfl,restrict_val]
  change LiteralIndependentFrameChange318.map N g ≫ LiteralIndependentPairFunctor318.first N=_
  rw [←frame_eq]
  exact LiteralIndependentFrameAction318.first N g
lemma pull_second (g:F3FrameChange318.Group) : pull N g (second N)=change g ![first N,second N] 1:=by
  apply Subtype.ext
  rw [show pull N g (second N)=restrict N (LiteralIndependentFrameChange318.map N g) (frameBase N)
    (LiteralIndependentSectionAction318.map_structure N g) (second N) from rfl,restrict_val]
  change LiteralIndependentFrameChange318.map N g ≫ LiteralIndependentPairFunctor318.second N=_
  rw [←frame_eq]
  exact LiteralIndependentFrameAction318.second N g
/-- Genuine universal coefficient transformation, in the full module of
Scheme-valued kernel points. No geometric point test is used. -/
theorem combination (g:F3FrameChange318.Group) (c:Standard) :
    pull N g (KernelUniversalFrame318.combination N c)=KernelUniversalFrame318.combination N (g c):=by
  rw [KernelUniversalFrame318.combination,map_add,map_smul,map_smul,pull_first,pull_second,
    F3FrameCoefficients318.change_coordinates,F3FrameCoefficients318.linearize_apply]
  rfl
@[reassoc] theorem combination_value (g:F3FrameChange318.Group) (c:Standard) :
    LiteralIndependentFrameChange318.map N g ≫ (KernelUniversalFrame318.combination N c).val=
      (KernelUniversalFrame318.combination N (g c)).val:=by
  have h:=congrArg Subtype.val (combination N g c)
  unfold pull at h
  rw [restrict_val] at h
  exact h
end KernelFrameChangeCoordinates318
