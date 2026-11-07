module
public import QuadraticBundleEquivalence318
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LocalFrameEmbedding318
open TangentCoordinates318 ActualQuadraticForm318 DerivativeCocycle318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace TangentMetric318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Complex tangent length dual to the source cotangent normalization 2 Imτ.
The ordinary real hyperbolic line element is twice this length. -/
@[expose] def lengthAt (z:UpperHalfPlane) (u:ℂ) : ℝ := ‖(show ℂ from u)‖/(2*z.im)

theorem derivative_im (g:G) (z:UpperHalfPlane) : (g • z).im=‖derivative g z‖*z.im := by
  change ((g:Matrix.GeneralLinearGroup (Fin 2) ℝ) • z).im=‖derivative g z‖*z.im
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  have hd:0<(g:Matrix.GeneralLinearGroup (Fin 2) ℝ).val.det:=by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.mem_glpos _).mp g.property
  simp only [derivative,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hd,Complex.normSq_eq_norm_sq,Matrix.GeneralLinearGroup.val_det_apply]
  change ((g:Matrix.GeneralLinearGroup (Fin 2) ℝ).val.det*z.im)/‖UpperHalfPlane.denom g z‖^2=
    (((g:Matrix.GeneralLinearGroup (Fin 2) ℝ).val.det)/‖UpperHalfPlane.denom g z‖^2)*z.im
  ring

/-- Actual derivative transport preserves the specified complex tangent metric. -/
theorem length_transport (g:G) (z:UpperHalfPlane) (u:ℂ) :
    lengthAt (g • z) (derivative g z*u)=lengthAt z u := by
  rw [lengthAt,lengthAt,norm_mul,derivative_im]
  have hd:‖derivative g z‖≠0:=norm_ne_zero_iff.mpr (derivative_ne_zero g z)
  field_simp

variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

/-- A genuine seminorm on the actual tangent fiber, with positive scale. -/
@[expose] def tangentSeminorm (b:Base (image N)) : Seminorm ℂ (TangentSpace 𝓘(ℂ) b) :=
  Seminorm.of (fun u=>lengthAt (chosenLift N b) (show ℂ from u))
    (by
      intro u v
      change ‖(show ℂ from u)+(show ℂ from v)‖/(2*(chosenLift N b).im)≤‖(show ℂ from u)‖/(2*(chosenLift N b).im)+‖(show ℂ from v)‖/(2*(chosenLift N b).im)
      rw [←add_div]
      exact div_le_div_of_nonneg_right (norm_add_le (show ℂ from u) (show ℂ from v)) (by positivity))
    (by
      intro c u
      change ‖c*(show ℂ from u)‖/(2*(chosenLift N b).im)=‖c‖*(‖(show ℂ from u)‖/(2*(chosenLift N b).im))
      rw [norm_mul,mul_div_assoc])

theorem tangentSeminorm_apply (b:Base (image N)) (u:TangentSpace 𝓘(ℂ) b) :
    tangentSeminorm N b u=‖(show ℂ from u)‖/(2*(chosenLift N b).im) := rfl

theorem tangentSeminorm_zero (b:Base (image N)) (u:TangentSpace 𝓘(ℂ) b) :
    tangentSeminorm N b u=0 ↔ u=0 := by
  rw [tangentSeminorm_apply,div_eq_zero_iff]
  have hy:2*(chosenLift N b).im≠0:=by positivity
  simp only [hy,or_false,norm_eq_zero]
  rfl

theorem chosen_sheet_lift (b:Base (image N)) :
    lift N hN.out (chosenLift N b) ⟨b,chosenLift_mem N hN.out b⟩=chosenLift N b := by
  change (quotient_localHomeomorph N hN.out).localInverseAt (chosenLift N b) b=chosenLift N b
  have hb:quotientMap N (chosenLift N b)=b:=(quotient_surjective N b).choose_spec
  calc
    _=(quotient_localHomeomorph N hN.out).localInverseAt (chosenLift N b) (quotientMap N (chosenLift N b)):=congrArg _ hb.symm
    _=chosenLift N b:=(quotient_localHomeomorph N hN.out).localInverseAt_apply_self

/-- The seminorm has the same value in every actual quotient tangent chart. -/
theorem tangent_chart_length (a:UpperHalfPlane) (b:Base (image N))
    (hb:b∈sheet N hN.out a) (u:TangentSpace 𝓘(ℂ) b) :
    tangentSeminorm N b u=
      lengthAt (lift N hN.out a ⟨b,hb⟩) (tangentFrame N a ⟨b,u⟩).2 := by
  let z:=chosenLift N b
  have hz:quotientMap N z=b:=(quotient_surjective N b).choose_spec
  have hza:quotientMap N z∈((quotient_localHomeomorph N hN.out).localInverseAt a).source:=by rw [hz];exact hb
  obtain ⟨g,hg,hd⟩:=CotangentTransition318.inverse_derivative_deck N hN.out _
    ((quotient_localHomeomorph N hN.out).localInverseAt_symm a) z hza
  have hg':(g:G) • z=lift N hN.out a ⟨b,hb⟩:=by
    change (g:G) • z=((quotient_localHomeomorph N hN.out).localInverseAt a) b
    rw [hz] at hg
    exact hg
  rw [tangent_frame_apply]
  have hc:localChart N hN.out (chosenLift N b) b=(z:ℂ):=
    congrArg UpperHalfPlane.coe (chosen_sheet_lift N b)
  have he:(((localChart N hN.out (chosenLift N b)).symm.trans (localChart N hN.out a)):ℂ→ℂ)=
      (fun w:ℂ=>((quotient_localHomeomorph N hN.out).localInverseAt a (quotientMap N (ofComplex w)):ℂ)) := by
    ext w
    simp only [OpenPartialHomeomorph.coe_trans,Function.comp_apply,localChart_apply,localChart_symm_apply]
  rw [he,hc,hd,←hg']
  exact (length_transport g z (show ℂ from u)).symm

end TangentMetric318
