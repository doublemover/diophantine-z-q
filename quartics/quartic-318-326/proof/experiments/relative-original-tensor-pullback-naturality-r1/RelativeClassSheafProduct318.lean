module
public import RelativeClassSheafPoint318
public section
noncomputable section
namespace RelativeClassSheafProduct318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open RelativeLineClassBaseChange318 RelativeClassSheafPoint318
variable {C S B : Scheme.{0}} (p : C ⟶ S) (b : B ⟶ S)

lemma original_mul (L N : Class C) : original p b (L*N)=original p b L*original p b N := by
  simp only [original,map_mul]
lemma value_mul (a d : TestClass p b) : value p b (a*d)=value p b a*value p b d :=
  map_mul ((RelativeFppfLineSheaf318.unit p).app (Opposite.op (Over.mk b))) a d

/-- Cancellation occurs in the EXISTING relative fppf sheaf group, not
in absolute line classes where a tautological base twist may remain. -/
lemma translated (a : TestClass p b) (L N : Class C)
    (h : value p b a=value p b (original p b (L*N))) :
    value p b a * (value p b (original p b N))⁻¹=value p b (original p b L) := by
  rw [h,original_mul,value_mul,mul_inv_cancel_right]
end RelativeClassSheafProduct318
