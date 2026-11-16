module
public import ComplexProjectiveMarkerPoint318
public import Mathlib.RingTheory.MvPolynomial.Ideal
public section
noncomputable section
namespace ComplexProjectiveVariableCover318
open AlgebraicGeometry ComplexProjectiveMarkerPoint318
variable {ι:Type*}
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra

lemma positive_homogeneous_in_variables(p:Equations (ι:=ι))(n:ℕ)(hn:0<n)
    (hp:p.IsHomogeneous n):p∈MvPolynomial.idealOfVars ι ℂ:=by
  rw [←pow_one (MvPolynomial.idealOfVars ι ℂ),MvPolynomial.mem_pow_idealOfVars_iff']
  intro m hm
  apply hp.coeff_eq_zero
  omega

/-- Every genuine projective prime omits one original variable. This
uses the full irrelevant ideal, not only the complex-valued points. -/
theorem exists_variable_nonmem(p:ProjectiveSpectrum (grading (ι:=ι))):
    ∃j:ι,MvPolynomial.X j∉p.asHomogeneousIdeal:=by
  by_contra h
  push_neg at h
  have hv:MvPolynomial.idealOfVars ι ℂ≤p.asHomogeneousIdeal.toIdeal:=by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact h j
  apply p.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn a ha
  exact hv (positive_homogeneous_in_variables a n hn ha)
end ComplexProjectiveVariableCover318
