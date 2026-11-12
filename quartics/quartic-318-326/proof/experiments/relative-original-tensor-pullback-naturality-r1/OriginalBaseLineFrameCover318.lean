module
public import OriginalAbsoluteLinePresheaf318
public section
noncomputable section
namespace OriginalBaseLineFrameCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {B : Scheme.{u}} (M : Line B)
/-- Use precisely the original line's own covering opens, with no choice
of a trivialization on points or replacement coefficient scheme. -/
@[expose] def cover : B.OpenCover where
  I₀ := M.Index
  X i := (M.opens i).toScheme
  f i := (M.opens i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (M.cover (show x∈(⊤:B.Opens) from trivial))
    exact ⟨i,⟨⟨x,hi⟩,rfl⟩⟩
/-- The specified original full restriction frame, transported through
the canonical restriction/pullback comparison, not a line-class choice. -/
@[expose] def frame (i : M.Index) : Frames (LineSheafPullback318.line (M.opens i).ι M) :=
  M.frame i ≪≫ (Scheme.Modules.restrictFunctorIsoPullback (M.opens i).ι).app M.object
lemma class_one (i : M.Index) :
    LineClassPullbackHom318.pullback (M.opens i).ι (classOf M)=1 :=
  classOf_eq (frame M i).symm
end OriginalBaseLineFrameCover318
