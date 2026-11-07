module
public import IntegralRingEvaluation318
public import ScaledClosedDisc318
public import InertIntegers318
public section
namespace InertClosedDisc318
open PowerSeries IntegralRingEvaluation318 InertIntegers318
variable (p : ℕ) [Fact p.Prime] (nonsquare : ¬∃x : ZMod p, x^2=2)

instance integralNormBound : NormBoundOne (Integers p nonsquare) where
  norm_le_one := InertIntegers318.norm_le_one p nonsquare

instance padicNormBound : NormBoundOne ℤ_[p] where
  norm_le_one := PadicInt.norm_le_one

/-- The general evaluator instantiated on the actual completed inert integral ring. -/
theorem eval_subst (f g : PowerSeries (Integers p nonsquare))
    (hf : IsRestricted 1 f) (hg : IsRestricted 1 g) (hg0 : constantCoeff g=0)
    (t : Integers p nonsquare) :
    eval (Integers p nonsquare) (f.subst g) t =
      eval (Integers p nonsquare) f (eval (Integers p nonsquare) g t) :=
  IntegralRingEvaluation318.eval_subst _ f g hf hg hg0 t

/-- Source-family coefficients for parameters in the Qp subfield, embedded isometrically.
For arbitrary inert D, use ArbitraryInertSeries318 instead. -/
@[expose] noncomputable def integral (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries (Integers p nonsquare) :=
  (ScaledFormalSeries318.integralScaled p hp D hD).map (padicIntEmbedding p nonsquare)

@[expose] noncomputable def branch (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries (Integers p nonsquare) :=
  (ScaledFormalSeries318.branchScaled p hp D hD).map (padicIntEmbedding p nonsquare)

theorem integral_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    IsRestricted 1 (integral p nonsquare hp D hD) :=
  restricted_map ℤ_[p] (padicIntEmbedding p nonsquare) (padicIntEmbedding_isometry p nonsquare)
    _ (ScaledClosedDisc318.integralScaled_restricted p hp D hD)

theorem branch_restricted (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    IsRestricted 1 (branch p nonsquare hp D hD) :=
  restricted_map ℤ_[p] (padicIntEmbedding p nonsquare) (padicIntEmbedding_isometry p nonsquare)
    _ (ScaledClosedDisc318.branchScaled_restricted p hp D hD)

/-- The integral evaluates by a genuinely convergent sum at every inert unit as well. -/
theorem integral_hasSum (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (t : Integers p nonsquare) :
    HasSum (fun n : ℕ => coeff n (integral p nonsquare hp D hD)*t^n)
      (eval (Integers p nonsquare) (integral p nonsquare hp D hD) t) :=
  eval_hasSum _ _ (integral_restricted p nonsquare hp D hD) t

theorem branch_hasSum (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (t : Integers p nonsquare) :
    HasSum (fun n : ℕ => coeff n (branch p nonsquare hp D hD)*t^n)
      (eval (Integers p nonsquare) (branch p nonsquare hp D hD) t) :=
  eval_hasSum _ _ (branch_restricted p nonsquare hp D hD) t

end InertClosedDisc318
#print axioms InertClosedDisc318.eval_subst
#print axioms InertClosedDisc318.integral_restricted
#print axioms InertClosedDisc318.branch_restricted
#print axioms InertClosedDisc318.integral_hasSum
