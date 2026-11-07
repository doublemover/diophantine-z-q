module
public import RingConjugateQuotient318
public section
noncomputable section
namespace RingInvolution318
set_option maxHeartbeats 300000
open PowerSeries RingConjugateQuotient318
variable {R:Type*} [CommRing R] [IsDomain R]

@[expose] def half (h2:IsUnit (2:R)) : R := ↑(h2.unit⁻¹)

theorem half_mul_two (h2:IsUnit (2:R)) : half h2*2=1 := by
  calc
    half h2*2 = (↑(h2.unit⁻¹):R)*↑h2.unit := by rw [h2.unit_spec];rfl
    _ = 1 := by simp

theorem constant_derivative (f:R⟦X⟧) : constantCoeff (derivative f)=coeff 1 f := by
  rw [←coeff_zero_eq_constantCoeff,coeff_derivative]
  simp

theorem coeff_one_subst (F f:R⟦X⟧) (hF:F.constantCoeff=0) :
    coeff 1 (f.subst F)=coeff 1 f*coeff 1 F := by
  rw [←constant_derivative,derivative_subst (HasSubst.of_constantCoeff_zero' hF),map_mul]
  have h0:=constantCoeff_subst_of_constantCoeff_zero (R:=R) hF (derivative f)
  change constantCoeff ((derivative f).subst F)=constantCoeff (derivative f) at h0
  rw [h0,constant_derivative,constant_derivative]

theorem identity_of_fixed_parameter (F H:R⟦X⟧) (hF:F.constantCoeff=0)
    (hH:H.constantCoeff=0) (hu:IsUnit (coeff 1 H)) (he:H.subst F=H) : F=X := by
  have hl:=subst_substInvOfIsUnit_left H hH hu
  have hc:=subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hH)
    (HasSubst.of_constantCoeff_zero' hF) (H.substInvOfIsUnit hu)
  rw [hl,subst_X (HasSubst.of_constantCoeff_zero' hF),he,hl] at hc
  exact hc

/-- Tangent-one involutions are trivial over an actual coefficient domain
with two a unit, not only over fields. -/
theorem identity_of_tangent_one (h2:IsUnit (2:R)) (F:R⟦X⟧)
    (hF:F.constantCoeff=0) (hp:F.subst F=X) (h1:coeff 1 F=1) : F=X := by
  let H:R⟦X⟧:=C (half h2)*(X+F)
  have hH:H.constantCoeff=0 := by simp [H,hF]
  have hH1:coeff 1 H=1 := by
    change coeff 1 (C (half h2)*(X+F))=1
    rw [coeff_C_mul,map_add,coeff_one_X,h1]
    convert half_mul_two h2 using 1 <;> ring
  have he:H.subst F=H := by
    have hs:=HasSubst.of_constantCoeff_zero' hF
    simp only [H,subst_mul hs,subst_add hs,subst_X hs,hp]
    have hc:PowerSeries.subst F (C (half h2))=C (half h2) := by
      rw [←coe_substAlgHom hs]
      exact (substAlgHom hs).commutes (half h2)
    rw [hc]
    ring
  exact identity_of_fixed_parameter F H hF hH (by rw[hH1];exact isUnit_one) he

theorem tangent_neg_one (h2:IsUnit (2:R)) (F:R⟦X⟧)
    (hF:F.constantCoeff=0) (hp:F.subst F=X) (hne:F≠X) : coeff 1 F= -1 := by
  have hh:=congrArg (coeff 1) hp
  rw [coeff_one_subst F F hF,coeff_one_X] at hh
  have hz:(coeff 1 F-1)*(coeff 1 F+1)=0 := by linear_combination hh
  rcases mul_eq_zero.mp hz with he|he
  · exact (hne (identity_of_tangent_one h2 F hF hp (sub_eq_zero.mp he))).elim
  · exact eq_neg_of_add_eq_zero_left he

/-- The normalized anti-invariant coordinate is explicitly (X-F)/2. -/
theorem normalized_parameter (h2:IsUnit (2:R)) (F:R⟦X⟧)
    (hF:F.constantCoeff=0) (hp:F.subst F=X) (hne:F≠X) :
    let H:=C (half h2)*(X-F)
    H.constantCoeff=0 ∧ coeff 1 H=1 ∧ H.subst F= -H := by
  dsimp only
  refine ⟨by simp [hF],?_,?_⟩
  · rw [coeff_C_mul,map_sub,coeff_one_X,tangent_neg_one h2 F hF hp hne]
    convert half_mul_two h2 using 1 <;> ring
  · have hs:=HasSubst.of_constantCoeff_zero' hF
    rw [subst_mul hs,subst_sub hs,subst_X hs,hp]
    have hc:PowerSeries.subst F (C (half h2))=C (half h2) := by
      rw [←coe_substAlgHom hs]
      exact (substAlgHom hs).commutes (half h2)
    rw [hc]
    ring

/-- Actual unique invariant-series descent over coefficient domains with two
invertible, including mixed-characteristic zero-constant formal charts. -/
theorem actual_invariant_quotient (h2:IsUnit (2:R)) (F:R⟦X⟧)
    (hF:F.constantCoeff=0) (hp:F.subst F=X) (hne:F≠X) :
    ∃H:R⟦X⟧,H.constantCoeff=0 ∧ coeff 1 H=1 ∧ H.subst F= -H ∧
      ∀f:R⟦X⟧,f.subst F=f ↔ ∃!g:R⟦X⟧,g.subst (H^2)=f := by
  obtain ⟨hH,h1,he⟩:=normalized_parameter h2 F hF hp hne
  refine ⟨C (half h2)*(X-F),hH,h1,he,?_⟩
  intro f
  exact fixed_iff_unique_square_parameter h2.ne_zero F _ hF hH
    (by rw[h1];exact isUnit_one) he f

end RingInvolution318
