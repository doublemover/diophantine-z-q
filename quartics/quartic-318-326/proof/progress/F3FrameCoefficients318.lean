module
public import F3FrameChange318
public section
noncomputable section
namespace F3FrameCoefficients318
open F3FrameChange318
variable {V:Type*} [AddCommGroup V] [Module (ZMod 3) V]
/-- The linear extension is the actual two-term coefficient sum. -/
theorem linearize_apply (v:Fin 2→V) (c:Standard) : linearize v c=c 0 • v 0+c 1 • v 1:=by
  rw [linearize,Module.Basis.constr_apply_fintype,Fin.sum_univ_two]
  simp only [standardBasis,Module.Basis.equivFun_apply,Pi.basisFun_repr]
/-- Fixed coordinates in a changed frame represent transformed
coordinates in the original frame. -/
theorem change_coordinates (g:F3FrameChange318.Group) (v:Fin 2→V) (c:Standard) :
    c 0 • change g v 0+c 1 • change g v 1=linearize v (g c):=by
  rw [←linearize_apply,linearize_change]
  rfl
end F3FrameCoefficients318
