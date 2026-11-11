module
public import ContactExplicitArithmeticModel318
public section
noncomputable section
namespace ContactArithmeticOriginalSource318
open Polynomial
open ContactArithmeticBase318 ContactArithmeticTwists318 IntegralSourceArithmeticDomain318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance polynomialAlgebra : Algebra (Base c)[X] ℚ[X] := (polynomialMap (Base c)).toAlgebra

theorem original_twists : rationalTwists (Base c) (twist c)=c := by
  funext i
  apply Units.ext
  exact twist_value c i

/-- The literal full finite source after rational base change is the
original four-root order with the original signed rational twists. -/
@[expose] def sourceBaseChange :
    ℚ[X] ⊗[(Base c)[X]] IntegralSourceBranches318.SourceOrder (Base c) (twist c)
      ≃ₐ[ℚ[X]] ContactKummerOrder318.SourceOrder c :=
  (rationalBaseChange (Base c) (twist c)).trans
    (presentationEquiv (congrArg ContactKummerOrder318.coefficient (original_twists c)))

/-- The actual arithmetic finite t-chart is rank16. This does not replace
the variable degree of a specialized point field by sixteen. -/
theorem source_rank : Module.finrank (Base c)[X]
    (IntegralSourceBranches318.SourceOrder (Base c) (twist c))=16 :=
  IntegralSectionPencilDegree318.rank_sixteen (Base c) (twist c)
end ContactArithmeticOriginalSource318
