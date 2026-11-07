module
public import RingEvenFormalQuotient318
public section
noncomputable section
namespace RingConjugateQuotient318
set_option maxHeartbeats 0
open PowerSeries TameCoordinate318 TameLinearization318 RingEvenFormalQuotient318
variable {k:Type*} [CommRing k] [IsDomain k]

/-- Substitution by an actual invertible parameter is injective. -/
theorem parameter_subst_injective (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) : Function.Injective (fun f:k⟦X⟧=>f.subst H) := by
  intro f g h
  have he:=congrArg (fun P:k⟦X⟧=>P.subst (H.substInvOfIsUnit hu)) h
  simpa only [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hH)
    (HasSubst.substInvOfIsUnit H hu),subst_substInvOfIsUnit_right H hH hu,X_subst] using he

/-- The actual inverse parameter recovers every series. -/
theorem inverse_parameter_cancel (H:k⟦X⟧) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) (f:k⟦X⟧) : PowerSeries.subst H (f.subst (H.substInvOfIsUnit hu))=f := by
  rw [subst_comp_subst_apply (HasSubst.substInvOfIsUnit H hu)
    (HasSubst.of_constantCoeff_zero' hH),subst_substInvOfIsUnit_left H hH hu,X_subst]

/-- Expansion in the squared normalized coordinate is actual composition. -/
theorem expand_subst_parameter (H:k⟦X⟧) (hH:H.constantCoeff=0) (g:k⟦X⟧) :
    (expand 2 (by decide) g).subst H=g.subst (H^2) := by
  rw [expand_apply,subst_comp_subst_apply (HasSubst.X_pow (by decide))
    (HasSubst.of_constantCoeff_zero' hH),subst_pow (HasSubst.of_constantCoeff_zero' hH),
    subst_X (HasSubst.of_constantCoeff_zero' hH)]

/-- The actual invariant series for a linearized involution are uniquely
series in the square of that invertible coordinate. -/
theorem fixed_iff_unique_square_parameter (h2:(2:k)≠0)
    (F H:k⟦X⟧) (hF:F.constantCoeff=0) (hH:H.constantCoeff=0)
    (hu:IsUnit (coeff 1 H)) (he:H.subst F= -H) (f:k⟦X⟧) :
    f.subst F=f ↔ ∃!g:k⟦X⟧,g.subst (H^2)=f := by
  have hHs:HasSubst H:=HasSubst.of_constantCoeff_zero' hH
  have hFs:HasSubst F:=HasSubst.of_constantCoeff_zero' hF
  have hNs:HasSubst (-X:k⟦X⟧):=HasSubst.of_constantCoeff_zero' (by simp)
  have hneg:(-X:k⟦X⟧).subst H= -H := by
    simpa only [neg_one_smul,subst_X hHs] using subst_smul hHs (-1:k) (X:k⟦X⟧)
  have hi:=parameter_subst_injective H hH hu
  constructor
  · intro hf
    let q:k⟦X⟧:=f.subst (H.substInvOfIsUnit hu)
    have hq:q.subst H=f:=inverse_parameter_cancel H hH hu f
    have hfix:q.subst (-X)=q := by
      apply hi
      calc
        PowerSeries.subst H (q.subst (-X)) = q.subst (-H) := by rw [subst_comp_subst_apply hNs hHs,hneg]
        _ = q.subst (H.subst F) := by rw [he]
        _ = PowerSeries.subst F (q.subst H) := (subst_comp_subst_apply hHs hFs q).symm
        _ = q.subst H := by rw [hq,hf]
    obtain ⟨g,hg,hgu⟩:=(subst_fixed_iff_existsUnique h2 q).mp hfix
    have hgf:g.subst (H^2)=f := by
      rw [←expand_subst_parameter H hH,expand_apply,hg,hq]
    refine ⟨g,hgf,?_⟩
    intro g' hg'
    apply expand_two_injective
    apply hi
    change (expand 2 (by decide) g').subst H = (expand 2 (by decide) g).subst H
    rw [expand_subst_parameter H hH,expand_subst_parameter H hH,hg',hgf]
  · rintro ⟨g,hg,_⟩
    calc
      f.subst F = PowerSeries.subst F (g.subst (H^2)) := by rw [hg]
      _ = g.subst ((H^2).subst F) := by
        rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (show constantCoeff (H^2)=0 by simp [hH])) hFs]
      _ = g.subst (H^2) := by rw [subst_pow hFs,he,neg_sq]
      _ = f := hg

end RingConjugateQuotient318
