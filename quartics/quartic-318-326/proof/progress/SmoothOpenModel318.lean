module
public import SmoothGenericField318
public import NormalAffineModel318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace SmoothOpenModel318
open Algebra
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
variable {R Rf K B:Type u} [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing Rf] [IsDomain Rf] [IsIntegrallyClosed Rf]
  [Algebra R Rf] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K] [Algebra Rf K] [IsFractionRing Rf K]
  [IsScalarTower R Rf K]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra Rf B]
  [IsScalarTower R Rf B] [Algebra.Smooth Rf B] [Module.Finite Rf B]

include Rf K in
/-- A genuine connected finite smooth open cover has a finite integral-closure
model over the unlocalized normal Noetherian base. Normality of the open
algebra and its generic field are constructed, not supplied. -/
theorem model_finite : Module.Finite R (integralClosure R B) := by
  let L:=B⊗[Rf]K
  let : Field L:=SmoothGenericField318.genericField (R:=Rf) (K:=K) (B:=B)
  let : Module.Finite K L:=SmoothGenericField318.generic_finite
  let : IsIntegrallyClosed B:=SmoothGenericField318.smooth_integrallyClosed (R:=Rf) (K:=K)
  let : IsFractionRing B L:=SmoothGenericField318.generic_fractionRing
  let : IsScalarTower R K L:=IsScalarTower.of_algebraMap_eq (by
    intro r
    change algebraMap R B r ⊗ₜ[Rf] (1:K)=(1:B)⊗ₜ[Rf]algebraMap R K r
    rw [IsScalarTower.algebraMap_apply R Rf B,IsScalarTower.algebraMap_apply R Rf K]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _)
  exact NormalAffineModel318.model_finite (K:=K) (L:=L)

include Rf K in
/-- The same actual model is normal, not merely a finite possibly nonnormal order. -/
theorem model_normal : IsIntegrallyClosed (integralClosure R B) := by
  let L:=B⊗[Rf]K
  let : Field L:=SmoothGenericField318.genericField (R:=Rf) (K:=K) (B:=B)
  let : IsIntegrallyClosed B:=SmoothGenericField318.smooth_integrallyClosed (R:=Rf) (K:=K)
  let : IsFractionRing B L:=SmoothGenericField318.generic_fractionRing
  let : IsIntegralClosure (integralClosure R B) R L:=
    NormalAffineModel318.model_integralClosure (L:=L)
  let : IsIntegrallyClosedIn (integralClosure R B) L:=
    IsIntegrallyClosedIn.of_isIntegralClosure (R:=R)
  let : FaithfulSMul (integralClosure R B) L:=
    IsIntegralClosure.faithfulSMul R (integralClosure R B) L
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure R B) L

end SmoothOpenModel318
