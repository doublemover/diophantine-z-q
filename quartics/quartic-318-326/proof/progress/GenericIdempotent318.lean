module
public import EtaleNormalization318
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic
public section
noncomputable section
namespace GenericIdempotent318
open Algebra
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R B K:Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing B] [Algebra R B] [Algebra.Smooth R B] [Module.Finite R B]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every actual generic-fiber idempotent is integral over the normal base. -/
theorem idempotent_integral (x:B⊗[R]K) (hx:IsIdempotentElem x) : IsIntegral R x := by
  refine ⟨Polynomial.X^2-Polynomial.X,?_,?_⟩
  · exact Polynomial.monic_X_pow_sub (by simp)
  · change Polynomial.eval₂ (algebraMap R (B⊗[R]K)) x (Polynomial.X^2-Polynomial.X)=0
    simp only [Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    exact sub_eq_zero.mpr (by simpa [pow_two,IsIdempotentElem] using hx)

/-- Generic idempotents descend uniquely to the actual finite smooth cover;
no connected-component or normality assumption on that cover is supplied. -/
theorem existsUnique_idempotent (x:B⊗[R]K) (hx:IsIdempotentElem x) :
    ∃! b:B, IsIdempotentElem b ∧ algebraMap B (B⊗[R]K) b=x := by
  letI:=EtaleNormalization318.smooth_finite_integralClosure (R:=R) (S:=B) (K:=K)
  obtain ⟨b,hb⟩:=(IsIntegralClosure.isIntegral_iff (R:=R) (A:=B) (B:=B⊗[R]K) (x:=x)).mp
    (idempotent_integral x hx)
  have hinj:Function.Injective (algebraMap B (B⊗[R]K)):=Algebra.TensorProduct.includeLeft_injective (S:=B) (IsFractionRing.injective R K)
  have hi:IsIdempotentElem b := by
    change b*b=b
    apply hinj
    simpa only [map_mul,hb] using (show x*x=x from hx)
  exact ⟨b,⟨hi,hb⟩,fun c hc=>hinj (hc.2.trans hb.symm)⟩
end GenericIdempotent318
