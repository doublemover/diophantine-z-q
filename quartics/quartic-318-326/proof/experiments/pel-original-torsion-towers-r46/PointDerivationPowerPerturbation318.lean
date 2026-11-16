module
public import AnalyticEvaluationDerivation318
public section
noncomputable section
namespace PointDerivationPowerPerturbation318
variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Powers of degree at least two of a centered actual chart element
have zero differential for EVERY derivation at the same complex point.
The scalar action is the original evaluation action, not transported. -/
theorem centered_power_zero (v : A →ₐ[ℂ] ℂ)
    (D : AnalyticEvaluationDerivation318.PointDerivations v) (b : A)
    (M : ℕ) (hM : 2 ≤ M) :
    D ((b-algebraMap ℂ A (v b))^M) = 0 := by
  letI : Module A ℂ := Module.compHom ℂ v.toRingHom
  rw [Derivation.leibniz_pow]
  change M • (v ((b-algebraMap ℂ A (v b))^(M-1)) * D (b-algebraMap ℂ A (v b))) = 0
  have hM0 : M-1 ≠ 0 := by omega
  simp only [map_pow,map_sub,AlgHom.commutes,sub_self,zero_pow hM0,zero_mul,smul_zero]

/-- The literal finite perturbation retains the prescribed first jet
at the specified actual evaluation, for all genuine point derivations. -/
theorem first_jet (v : A →ₐ[ℂ] ℂ)
    (D : AnalyticEvaluationDerivation318.PointDerivations v) (b l : A)
    (M : ℕ) (hM : 2 ≤ M) :
    D (l+(b-algebraMap ℂ A (v b))^M) = D l := by
  rw [map_add,centered_power_zero v D b M hM,add_zero]
end PointDerivationPowerPerturbation318
