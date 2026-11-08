module
public import ComplementSquareclass318
public section
noncomputable section
namespace SourceTwistRecovery318
set_option maxHeartbeats 600000
open SourceTwistArithmetic318 ComplementSquareclass318

/-- The coefficient equations of an actual short-Weierstrass isomorphism
determine the twist up to the square of its coordinate scale. -/
theorem twist_of_coefficient_scaling {F:Type*} [Field F]
    (A B c d u:F) (hA:A≠0) (hB:B≠0) (hc:c≠0) (hd:d≠0) (hu:u≠0)
    (h4:c^2*A=u^4*(d^2*A)) (h6:c^3*B=u^6*(d^3*B)) : c=d*u^2 := by
  have h4':c^2=u^4*d^2:=mul_right_cancel₀ hA (by simpa only [mul_assoc] using h4)
  have h6':c^3=u^6*d^3:=mul_right_cancel₀ hB (by simpa only [mul_assoc] using h6)
  calc
    c=c^3/c^2 := by field_simp [hc]
    _=(u^6*d^3)/(u^4*d^2) := by rw [h4',h6']
    _=d*u^2 := by field_simp [hd,hu]

theorem cubic_coefficients_nonzero (i:Fin 4) : cubicA i≠0 ∧ cubicB i≠0 := by
  fin_cases i <;> norm_num [cubicA,cubicB]
theorem published_twist_nonzero (i:Fin 4) : jacobianTwist i≠0 := by
  fin_cases i <;> norm_num [jacobianTwist]
theorem scale_nonzero (i:Fin 4) : coordinateScale i≠0 := by
  fin_cases i <;> norm_num [coordinateScale]

/-- This is the exact remaining arithmetic interface to the geometric
Jacobian comparison. Its hypothesis asks for actual rational coordinate
scalings, not just equal j-invariants or isogenous Jacobians. -/
theorem recover_source_twists (a:Fin 4→ℚ) (ha:∀i,a i≠0)
    (h:∀i,∃u:ℚ,u≠0 ∧
      complementaryProduct a i^2*cubicA i=u^4*publishedA i ∧
      complementaryProduct a i^3*cubicB i=u^6*publishedB i) :
    ∀i,IsSquare (a i/constants i) := by
  apply recover_twist_ratios a constants ha constants_ne_zero
  intro i
  obtain ⟨u,hu,h4,h6⟩:=h i
  rw [(published_twist_exact i).1] at h4
  rw [(published_twist_exact i).2] at h6
  have hc:complementaryProduct a i≠0:=
    Finset.prod_ne_zero_iff.mpr (fun j _=>ha (complement i j))
  have he:=twist_of_coefficient_scaling (cubicA i) (cubicB i)
    (complementaryProduct a i) (jacobianTwist i) u
    (cubic_coefficients_nonzero i).1 (cubic_coefficients_nonzero i).2
    hc (published_twist_nonzero i) hu h4 h6
  change IsSquare (complementaryProduct a i/twistProducts i)
  rw [he,complementary_twist_exact]
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨u/coordinateScale i,?_⟩
  field_simp [published_twist_nonzero i,scale_nonzero i]
end SourceTwistRecovery318
