module
public import ThreeJDerivativeComparison318
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace ThreeJQuotientDerivation318
open Polynomial ThreeJMonicAlgebra318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def evaluation : Base[X] →ₐ[Base] Model := Polynomial.aeval t
lemma evaluation_mk (q : Base[X]) : evaluation q=AdjoinRoot.mk polynomial q :=
  AdjoinRoot.aeval_eq q
lemma evaluation_surjective : Function.Surjective evaluation := by
  intro a
  obtain ⟨q,hq⟩ := (show Function.Surjective (AdjoinRoot.mk polynomial) from
    AdjoinRoot.mk_surjective) a
  exact ⟨q,(evaluation_mk q).trans hq⟩
lemma evaluation_polynomial : evaluation polynomial=0 := by
  rw [evaluation_mk,AdjoinRoot.mk_self]

@[expose] def delta : Model := evaluation polynomial.derivative
@[expose] def derivativeIdeal : Ideal Model := Ideal.span {delta}
abbrev DifferentialQuotient := Model ⧸ derivativeIdeal
@[expose] def quotientMap : Model →ₐ[Base] DifferentialQuotient :=
  Ideal.Quotient.mkₐ Base derivativeIdeal

lemma quotient_delta : quotientMap delta=0 := by
  change Ideal.Quotient.mk derivativeIdeal delta=0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- Polynomial differentiation followed by the actual quotient by the
monic derivative, before descending through the original quartic relation. -/
@[expose] def polynomialDifferential : Base[X] →ₗ[Base] DifferentialQuotient :=
  quotientMap.toLinearMap.comp (evaluation.toLinearMap.comp Polynomial.derivative'.toLinearMap)
lemma polynomialDifferential_apply (q : Base[X]) :
    polynomialDifferential q=quotientMap (evaluation q.derivative) := rfl

lemma descends : LinearMap.ker evaluation.toLinearMap ≤ LinearMap.ker polynomialDifferential := by
  intro q hq
  change evaluation q=0 at hq
  rw [evaluation_mk,AdjoinRoot.mk_eq_zero] at hq
  obtain ⟨r,rfl⟩ := hq
  change quotientMap (evaluation (polynomial*r).derivative)=0
  rw [derivative_mul]
  simp only [map_add,map_mul,evaluation_polynomial,map_zero,zero_mul,mul_zero,add_zero]
  change quotientMap delta*quotientMap (evaluation r)=0
  rw [quotient_delta,zero_mul]

@[expose] def descendedLinear : Model →ₗ[Base] DifferentialQuotient :=
  (LinearMap.liftOfSurjective (f:=evaluation.toLinearMap) evaluation_surjective)
    ⟨polynomialDifferential,descends⟩
lemma descendedLinear_evaluation (q : Base[X]) :
    descendedLinear (evaluation q)=quotientMap (evaluation q.derivative) := by
  exact LinearMap.equivOfSurjective_apply (f:=evaluation.toLinearMap) evaluation_surjective descends

/-- A genuine relative derivation on the original quartic algebra, with
values in its derivative quotient. It detects the full relation in Omega. -/
@[expose] def quotientDerivation : Derivation Base Model DifferentialQuotient where
  toLinearMap := descendedLinear
  map_one_eq_zero' := by
    rw [←map_one evaluation,descendedLinear_evaluation,derivative_one,map_zero,map_zero]
  leibniz' a b := by
    obtain ⟨q,rfl⟩ := evaluation_surjective a
    obtain ⟨r,rfl⟩ := evaluation_surjective b
    rw [←map_mul evaluation,descendedLinear_evaluation,
      descendedLinear_evaluation,descendedLinear_evaluation,derivative_mul]
    simp only [map_add,map_mul,Algebra.smul_def]
    change quotientMap (evaluation q.derivative)*quotientMap (evaluation r)+
        quotientMap (evaluation q)*quotientMap (evaluation r.derivative)=
      quotientMap (evaluation q)*quotientMap (evaluation r.derivative)+
        quotientMap (evaluation r)*quotientMap (evaluation q.derivative)
    ring

lemma quotientDerivation_t : quotientDerivation t=1 := by
  change descendedLinear t=1
  have hx : evaluation X=t := Polynomial.aeval_X t
  rw [←hx,descendedLinear_evaluation,derivative_X,map_one,map_one]

end ThreeJQuotientDerivation318
