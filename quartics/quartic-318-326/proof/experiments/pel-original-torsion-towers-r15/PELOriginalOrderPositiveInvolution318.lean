module
public import PELOriginalFppfRosatiEquivariance318
public section
noncomputable section
namespace PELOriginalOrderPositiveInvolution318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318
open PELOriginalOrderHermitianAdjoint318
lemma involutive (a : order) : adjoint (adjoint a)=a := by
  apply Subtype.ext
  exact rosati_involutive a
lemma additive (a b : order) : adjoint (a+b)=adjoint a+adjoint b := by
  apply Subtype.ext
  exact rosati_add a b
lemma antimultiplicative (a b : order) : adjoint (a*b)=adjoint b*adjoint a := by
  apply Subtype.ext
  exact rosati_mul a b
lemma zero : adjoint (0 : order)=0 := by
  apply Subtype.ext
  simp [adjoint,rosati_coordinates]
lemma one : adjoint (1 : order)=1 := by
  apply Subtype.ext
  simp [adjoint,rosati_coordinates]
/-- The actual involution of the whole original order, with its additive
inverse and literal noncommutative multiplication reversal. -/
@[expose] def equivalence : order ≃+ order where
  toFun := adjoint
  invFun := adjoint
  left_inv := involutive
  right_inv := involutive
  map_add' := additive
lemma integer (n : ℤ) : adjoint (n : order)=(n : order) := by
  have h := map_zsmul equivalence.toAddMonoidHom (1 : order) n
  simpa only [zsmul_one,one] using h
/-- Positivity is the original rational quaternion reduced trace, not
a numerical trace assigned to an unrelated endomorphism model. -/
lemma positive (a : order) (ha : a≠0) :
    0<reducedTrace ((a:B)*(adjoint a:B)) := by
  apply positive_trace
  intro h
  apply ha
  apply Subtype.ext
  exact h
lemma trace_formula (a : order) :
    reducedTrace ((a:B)*(adjoint a:B))=
      2*((a:B).re^2+210*(a:B).imI^2+5*(a:B).imJ^2+1050*(a:B).imK^2) :=
  positive_trace_formula a
end PELOriginalOrderPositiveInvolution318
