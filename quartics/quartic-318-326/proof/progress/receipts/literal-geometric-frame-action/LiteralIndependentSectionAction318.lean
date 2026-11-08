module
public import LiteralIndependentFrameAction318
public import LiteralIndependentPairFinite318
public section
noncomputable section
namespace LiteralIndependentSectionAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 (Points)
open LiteralKernelAddition318 F3FrameChange318 LiteralIndependentPairOpen318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {X:Scheme} (b:X ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
abbrev Sections := {f:X ⟶ scheme N // f ≫ LiteralIndependentPairFinite318.structureMap N=b}
@[reassoc] theorem map_structure (g:F3FrameChange318.Group) :
    LiteralIndependentFrameChange318.map N g ≫ LiteralIndependentPairFinite318.structureMap N=
    LiteralIndependentPairFinite318.structureMap N:=by
  rw [LiteralIndependentPairFinite318.structureMap,←Category.assoc,
    LiteralIndependentFrameChange318.map_inclusion,Category.assoc,LiteralKernelFrameChange318.map_base]
@[expose] def action (g:F3FrameChange318.Group) (s:Sections N b) : Sections N b:=
  ⟨s.val ≫ LiteralIndependentFrameChange318.map N g,by rw [Category.assoc,map_structure,s.property]⟩
@[simp] theorem action_val (g:F3FrameChange318.Group) (s:Sections N b) :
    (action N b g s).val=s.val ≫ LiteralIndependentFrameChange318.map N g:=rfl
@[expose] def restrict (s:Sections N b) : Points N (productBase N) →ₗ[ZMod 3] Points N b:=
  LiteralKernelPointBaseTransport318.pull N (s.val ≫ inclusion N) (productBase N) b (by
    rw [Category.assoc]
    exact s.property)
@[simp] theorem restrict_val (s:Sections N b) (p:Points N (productBase N)) :
    (restrict N b s p).val=(s.val ≫ inclusion N) ≫ p.val:=
  LiteralKernelPointBaseTransport318.pull_val _ _ _ _ _ _
@[expose] def frame (s:Sections N b) : Fin 2→Points N b:=
  fun i=>restrict N b s (LiteralKernelFrameChange318.frame N i)
@[simp] theorem frame_val (s:Sections N b) (i:Fin 2) :
    (frame N b s i).val=(s.val ≫ inclusion N) ≫ (LiteralKernelFrameChange318.frame N i).val:=
  restrict_val N b s _
@[simp] theorem first_value (s:Sections N b) :
    (frame N b s 0).val=s.val ≫ LiteralIndependentPairFunctor318.first N:=by
  rw [frame_val,LiteralIndependentPairFunctor318.first,Category.assoc]
  rfl
@[simp] theorem second_value (s:Sections N b) :
    (frame N b s 1).val=s.val ≫ LiteralIndependentPairFunctor318.second N:=by
  rw [frame_val,LiteralIndependentPairFunctor318.second,Category.assoc]
  rfl
/-- The exact two original kernel sections determine the actual frame map. -/
theorem frame_injective : Function.Injective (frame N b):=by
  intro s t h
  apply Subtype.ext
  apply (cancel_mono (inclusion N)).mp
  apply pullback.hom_ext
  · have hh:=congrArg Subtype.val (congrFun h 0)
    simpa only [frame_val,LiteralKernelFrameChange318.frame,Matrix.cons_val_zero,leftPoint] using hh
  · have hh:=congrArg Subtype.val (congrFun h 1)
    simpa only [frame_val,LiteralKernelFrameChange318.frame,Matrix.cons_val_one,Matrix.cons_val_zero,rightPoint] using hh
/-- Actual equivariance over any fixed base map, not only geometric tests. -/
theorem frame_action (g:F3FrameChange318.Group) (s:Sections N b) :
    frame N b (action N b g s)=change g (frame N b s):=by
  funext i
  apply Subtype.ext
  have hn:change g (frame N b s) i=restrict N b s (change g (LiteralKernelFrameChange318.frame N) i):=by
    unfold frame
    exact (change_natural (restrict N b s) g (LiteralKernelFrameChange318.frame N) i).symm
  rw [hn,frame_val,restrict_val]
  have hm:=congrArg Subtype.val (congrFun (LiteralKernelFrameChange318.pull_frame N g) i)
  rw [LiteralKernelFrameChange318.pull_val] at hm
  rw [action_val]
  simp only [Category.assoc,LiteralIndependentFrameChange318.map_inclusion_assoc,hm]
@[simp] theorem action_one (s:Sections N b) : action N b 1 s=s:=by
  apply Subtype.ext
  simp only [action_val,LiteralIndependentFrameChange318.map_one,Category.comp_id]
theorem action_mul (g h:F3FrameChange318.Group) (s:Sections N b) :
    action N b h (action N b g s)=action N b (g*h) s:=by
  apply Subtype.ext
  simp only [action_val,Category.assoc,LiteralIndependentFrameChange318.map_mul]
end LiteralIndependentSectionAction318
