module
public import QuaternionicUnitPeriodTransport318
public section
noncomputable section
namespace QuaternionicPeriodAutomorphy318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicUnitPeriodTransport318
set_option maxHeartbeats 1200000
@[expose] def numerator (g : RealMatrices) (τ : ℂ) : ℂ := (g 0 0:ℂ)*τ+(g 0 1:ℂ)

/-- Exact automorphy-factor cocycle, with the order of the two real matrices
fixed by the original Möbius action. -/
theorem denominator_cocycle (g h : RealMatrices) (τ : ℂ) (hh : denominator h τ≠0) :
    denominator g (mobius h τ)*denominator h τ=denominator (g*h) τ := by
  have he : denominator h τ=(h 1 0:ℂ)*τ+(h 1 1:ℂ) := rfl
  have hn : (h 1 0:ℂ)*τ+(h 1 1:ℂ)≠0 := hh
  simp only [denominator,mobius,Matrix.mul_apply,Fin.sum_univ_two,
    Complex.ofReal_add,Complex.ofReal_mul]
  field_simp [hn]
  <;> ring

theorem numerator_cocycle (g h : RealMatrices) (τ : ℂ) (hh : denominator h τ≠0) :
    numerator g (mobius h τ)*denominator h τ=numerator (g*h) τ := by
  have hn : (h 1 0:ℂ)*τ+(h 1 1:ℂ)≠0 := hh
  simp only [numerator,denominator,mobius,Matrix.mul_apply,Fin.sum_univ_two,
    Complex.ofReal_add,Complex.ofReal_mul]
  field_simp [hn]
  <;> ring

theorem mobius_comp (g h : RealMatrices) (hg : g.det=1) (hh : h.det=1)
    (τ : ℂ) (hτ : 0<τ.im) : mobius g (mobius h τ)=mobius (g*h) τ := by
  have hd := denominator_ne h hh τ hτ
  have hg' := denominator_ne g hg (mobius h τ) (mobius_positive h hh τ hτ)
  have he := denominator_cocycle g h τ hd
  have hgh : denominator (g*h) τ≠0 := he ▸ mul_ne_zero hg' hd
  change numerator g (mobius h τ)/denominator g (mobius h τ)=
    numerator (g*h) τ/denominator (g*h) τ
  apply (div_eq_div_iff hg' hgh).mpr
  rw [←he,←numerator_cocycle g h τ hd]
  ring

/-- The actual fiber scalars satisfy the same cocycle, not only their
absolute values or their induced action on the rational span. -/
theorem scalar_cocycle (g h : RealMatrices) (τ : ℂ) (hh : denominator h τ≠0)
    (z : ComplexVectors) :
    (denominator g (mobius h τ))⁻¹ • ((denominator h τ)⁻¹ • z)=
      (denominator (g*h) τ)⁻¹ • z := by
  rw [smul_smul,←mul_inv,denominator_cocycle g h τ hh]

variable {B : Type*} [Ring B] (ρ : B →+* RealMatrices) (O : Subring B)

theorem unitMatrix_mul (u v : Oˣ) :
    unitMatrix ρ O (u*v)=unitMatrix ρ O u*unitMatrix ρ O v :=
  (ρ.comp O.subtype).map_mul (u:O) (v:O)

/-- Coherence at the original arithmetic units, needed before descending a
family. This is not yet a quotient family or its algebraization. -/
theorem unit_parameter_comp (u v : Oˣ) (hu : (unitMatrix ρ O u).det=1)
    (hv : (unitMatrix ρ O v).det=1) (τ : ℂ) (hτ : 0<τ.im) :
    unitParameter ρ O u (unitParameter ρ O v τ)=unitParameter ρ O (u*v) τ := by
  unfold unitParameter
  rw [unitMatrix_mul]
  exact mobius_comp _ _ hu hv τ hτ

theorem unit_scalar_cocycle (u v : Oˣ) (hv : (unitMatrix ρ O v).det=1)
    (τ : ℂ) (hτ : 0<τ.im) (z : ComplexVectors) :
    (unitDenominator ρ O u (unitParameter ρ O v τ))⁻¹ •
      ((unitDenominator ρ O v τ)⁻¹ • z)=
      (unitDenominator ρ O (u*v) τ)⁻¹ • z := by
  unfold unitDenominator unitParameter
  rw [unitMatrix_mul]
  exact scalar_cocycle _ _ τ (denominator_ne _ hv τ hτ) z
end QuaternionicPeriodAutomorphy318
