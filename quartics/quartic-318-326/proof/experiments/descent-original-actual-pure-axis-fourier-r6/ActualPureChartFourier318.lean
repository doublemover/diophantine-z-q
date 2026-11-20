module
public import ActualPureChartAxes318
public import ActualAxisFourthDecay318
import all ActualPureChartAxes318
import all ActualPureChartKernel318
import all ActualAxisFourthDecay318
public section
noncomputable section
namespace ActualPureChartFourier318
open MeasureTheory
open scoped FourierTransform ENNReal
open AffineThreePoissonRows318 ActualPureChartKernel318
open ActualAxisFourthDecay318 ActualPureChartAxes318

def vol₂ : Measure Outer := (volume:Measure ℝ).prod volume

/-- The three PAIR/ROW product orderings. These are actual measure
permutations, not alterations of the weight or accepted arithmetic fibre. -/
def perm : Axis → Outer×ℝ ≃ᵐ FreePoint
  | .z => MeasurableEquiv.prodAssoc
  | .t => MeasurableEquiv.prodAssoc.trans
       ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm)
  | .v => MeasurableEquiv.prodComm

private theorem inner_swap_preserves :
    MeasurePreserving (((MeasurableEquiv.refl ℝ).prodCongr
      MeasurableEquiv.prodComm):FreePoint≃ᵐ FreePoint) measure3 measure3 := by
  refine ⟨MeasurableEquiv.measurable _,?_⟩
  change Measure.map (Prod.map id Prod.swap)
    ((volume:Measure ℝ).prod ((volume:Measure ℝ).prod volume))=_
  rw [←Measure.map_prod_map _ _ measurable_id measurable_swap,Measure.map_id,
    Measure.prod_swap] <;> rfl

private theorem perm_preserves (axis : Axis) :
    MeasurePreserving (perm axis) (vol₂.prod (volume:Measure ℝ)) measure3 := by
  cases axis
  · exact measurePreserving_prodAssoc _ _ _
  · exact inner_swap_preserves.comp (measurePreserving_prodAssoc _ _ _)
  · exact Measure.measurePreserving_swap

def selected (axis : Axis) (ξ η ζ : ℝ) : ℝ :=
  match axis with | .z => ξ | .t => η | .v => ζ

def outerAngle (axis : Axis) (ξ η ζ : ℝ) (p : Outer) : ℝ :=
  match axis with
  | .z => p.1*ζ+p.2*η
  | .t => p.1*ζ+p.2*ξ
  | .v => p.1*η+p.2*ξ

private theorem kernel_axis (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer) (s : ℝ) :
    kernel κ τ X i (perm axis (p,s)) = row κ τ X i axis p s := by
  cases axis <;> rfl

private theorem tilt_axis (κ τ X : ℝ) (i : Fin 4)
    (axis : Axis) (ξ η ζ : ℝ) (p : Outer) (s : ℝ) :
    tilt κ τ X i ξ η ζ (perm axis (p,s)) =
      phase (-outerAngle axis ξ η ζ p)*(phase (-(s*selected axis ξ η ζ))*row κ τ X i axis p s) := by
  have h := kernel_axis κ τ X i axis p s
  rw [tilt,h,←mul_assoc,←phase_add]
  congr 1
  cases axis <;> simp [perm,outerAngle,selected] <;> ring

private theorem row_phase_integral (κ τ X : ℝ) (i : Fin 4)
    (axis : Axis) (ξ η ζ : ℝ) (p : Outer) :
    (∫ s,tilt κ τ X i ξ η ζ (perm axis (p,s))) =
      phase (-outerAngle axis ξ η ζ p)*
        𝓕 (row κ τ X i axis p) (selected axis ξ η ζ) := by
  simp_rw [tilt_axis]
  rw [integral_const_mul,Real.fourier_real_eq]
  simp only [phase,Circle.smul_def,smul_eq_mul]

private theorem volume_symmetric (R : ℝ) (hR : 0≤R) :
    (volume:Measure ℝ).real (symmetric R)=2*R := by
  rw [symmetric,Real.volume_real_Icc_of_le (by linarith : -R≤R)]
  ring

private theorem outer_volume (axis : Axis) (τ : ℝ) (hτ : 0<τ) :
    vol₂.real (outerBox axis τ)=(2*outerR₁ axis τ)*8 := by
  simp only [vol₂,outerBox,Measure.real_def,Measure.prod_prod,ENNReal.toReal_mul]
  change (volume:Measure ℝ).real (symmetric (outerR₁ axis τ))*
    (volume:Measure ℝ).real (symmetric 4)=_
  rw [volume_symmetric _ (radius_nonneg axis τ hτ).2,volume_symmetric 4 (by norm_num)]
  ring

private theorem whole_volume_identity (axis : Axis) (τ : ℝ) :
    ((2*outerR₁ axis τ)*8)*(2*rowR axis τ)=256*τ := by
  cases axis <;> simp only [outerR₁,rowR] <;> ring

/-- Uniform one-axis bound for any named physical component. The row
length and outer area multiply to 256τ for EACH of Z,T,V. -/
theorem F₃_axis_bound (κ τ X : ℝ) (i : Fin 4)
    (axis : Axis) (ξ η ζ J₀ J₄ : ℝ) (hτ : 0<τ)
    (h₀ : ∀ p s, ‖row κ τ X i axis p s‖≤J₀)
    (h₄ : ∀ p s, ‖iteratedDeriv 4 (row κ τ X i axis p) s‖≤J₄) :
    ‖F₃ (W κ τ i X) ξ η ζ‖≤
      (256*τ)*(J₀+((2*Real.pi)^4)⁻¹*J₄)/(1+|selected axis ξ η ζ|^4) := by
  let g := fun p : Outer×ℝ => tilt κ τ X i ξ η ζ (perm axis p)
  let q := selected axis ξ η ζ
  let C := (2*rowR axis τ)*(J₀+((2*Real.pi)^4)⁻¹*J₄)
  have hi : Integrable g (vol₂.prod (volume:Measure ℝ)) :=
    (perm_preserves axis).integrable_comp_of_integrable (tilt_integrable κ τ X i hτ ξ η ζ)
  have he : F₃ (W κ τ i X) ξ η ζ = ∫ p,g p ∂(vol₂.prod (volume:Measure ℝ)) := by
    rw [actual_F₃_tilt κ τ X i hτ ξ η ζ]
    exact ((perm_preserves axis).integral_comp' (tilt κ τ X i ξ η ζ)).symm
  have hr (p : Outer) :
      ‖𝓕 (row κ τ X i axis p) q‖≤C/(1+|q|^4) := by
    apply quartic_row_bound ((row_smooth κ τ X i axis p).of_le (by simp))
      (fun n _ => row_deriv_integrable κ τ X i axis p n hτ)
    have h0 := row_L1 κ τ X i axis p 0 hτ J₀ (by
      simpa only [iteratedDeriv_zero] using h₀ p)
    have h4 := row_L1 κ τ X i axis p 4 hτ J₄ (h₄ p)
    simp only [iteratedDeriv_zero] at h0
    exact (add_le_add h0 (mul_le_mul_of_nonneg_left h4 (by positivity))).trans_eq (by
      dsimp [C]
      ring)
  have hK := outerBox_compact axis τ
  have hb := integrated_axis_bound g hi (outerBox axis τ) hK.isClosed.measurableSet
    hK.measure_ne_top C q
    (fun p hp => by
      change (∫ s, tilt κ τ X i ξ η ζ (perm axis (p,s)))=0
      rw [row_phase_integral, row_zero_outside_outer κ τ X i axis p hτ hp]
      simp)
    (fun p _ => by
      change ‖∫ s,tilt κ τ X i ξ η ζ (perm axis (p,s))‖≤_
      rw [row_phase_integral,norm_mul]
      simpa [q,phase,Circle.norm_coe] using hr p)
  rw [he]
  apply hb.trans_eq
  rw [outer_volume axis τ hτ]
  dsimp only [C,q]
  rw [show ((2*outerR₁ axis τ)*8)*((2*rowR axis τ)*(J₀+((2*Real.pi)^4)⁻¹*J₄)/
       (1+|selected axis ξ η ζ|^4)) =
     ((((2*outerR₁ axis τ)*8)*(2*rowR axis τ))*(J₀+((2*Real.pi)^4)⁻¹*J₄))/
       (1+|selected axis ξ η ζ|^4) by ring,whole_volume_identity]

private theorem pure_uniform_all (κ τ : ℝ) (i : Fin 4) (n : ℕ) (hτ : 0<τ) :
    ∃ J : ℝ, 1≤J ∧ ∀ X axis p s, ‖iteratedDeriv n (row κ τ X i axis p) s‖≤J := by
  obtain ⟨Jz,hz,bz⟩ := pure_uniform κ τ i .z n hτ
  obtain ⟨Jt,_,bt⟩ := pure_uniform κ τ i .t n hτ
  obtain ⟨Jv,_,bv⟩ := pure_uniform κ τ i .v n hτ
  refine ⟨max Jz (max Jt Jv),hz.trans (le_max_left _ _),?_⟩
  intro X a p s
  cases a
  · exact (bz X p s).trans (le_max_left _ _)
  · exact (bt X p s).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (bv X p s).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem largest_axis (ξ η ζ : ℝ) :
    ∃ axis, |selected axis ξ η ζ|=max |ξ| (max |η| |ζ|) := by
  by_cases h : max |η| |ζ| ≤ |ξ|
  · exact ⟨.z,(max_eq_left h).symm⟩
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
    by_cases ht : |ζ| ≤ |η|
    · exact ⟨.t,(max_eq_left ht).symm⟩
    · exact ⟨.v,(max_eq_right (le_of_lt (lt_of_not_ge ht))).symm⟩

/-- Actual largest-frequency decay for the literal signed chart, with
no Poisson-row swap or order-(2,2,2) assumption. Fixed τ>0. -/
theorem exists_actual_F₃_shell (κ τ : ℝ) (i : Fin 4) (hτ : 0<τ) :
    ∃ C : ℝ, 0≤C ∧ ∀ X ξ η ζ,
      ‖F₃ (W κ τ i X) ξ η ζ‖≤C/(1+max |ξ| (max |η| |ζ|))^4 := by
  obtain ⟨J₀,hJ₀,b₀⟩ := pure_uniform_all κ τ i 0 hτ
  obtain ⟨J₄,hJ₄,b₄⟩ := pure_uniform_all κ τ i 4 hτ
  let C := (256*τ)*(J₀+((2*Real.pi)^4)⁻¹*J₄)
  have hC : 0≤C := by
    have h0 : 0≤J₀ := by linarith
    have h4 : 0≤J₄ := by linarith
    unfold C
    positivity
  refine ⟨8*C,mul_nonneg (by norm_num) hC,?_⟩
  intro X ξ η ζ
  obtain ⟨axis,ha⟩ := largest_axis ξ η ζ
  have h := F₃_axis_bound κ τ X i axis ξ η ζ J₀ J₄ hτ
    (by simpa only [iteratedDeriv_zero] using b₀ X axis) (b₄ X axis)
  rw [ha] at h
  exact h.trans (quartic_to_shell C _ hC ((abs_nonneg ξ).trans (le_max_left _ _)))

end ActualPureChartFourier318
