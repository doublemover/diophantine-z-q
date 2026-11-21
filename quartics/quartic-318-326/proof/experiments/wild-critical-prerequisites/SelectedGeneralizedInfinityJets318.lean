module
public import SelectedGeneralizedJCurve318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public section
noncomputable section

namespace SelectedGeneralizedInfinityJets318

/-- The actual homogeneous Weierstrass equation in the Y=1 chart:
over any square-zero ideal the infinity coordinates (X/Y,Z/Y)
have exactly the single first-order condition Z/Y=0. No coefficient
of W and no residue characteristic is excluded. -/
theorem infinity_equation_iff {D : Type*} [CommRing D]
    (W : WeierstrassCurve D) (u v : D) (hu : u*u = 0) (hv : v*v = 0)
    (huv : u*v = 0) :
    W.toProjective.Equation ![u,1,v] ↔ v = 0 := by
  rw [WeierstrassCurve.Projective.equation_iff]
  change (1:D)^2*v + W.a₁*u*1*v + W.a₃*1*v^2 -
    (u^3 + W.a₂*u^2*v + W.a₄*u*v^2 + W.a₆*v^3) = 0 ↔ v = 0
  have hu2 : u^2=0 := by rw [pow_two,hu]
  have hv2 : v^2=0 := by rw [pow_two,hv]
  have hu3 : u^3=0 := by rw [show (3:ℕ)=2+1 by decide,pow_succ,hu2,zero_mul]
  have hv3 : v^3=0 := by rw [show (3:ℕ)=2+1 by decide,pow_succ,hv2,zero_mul]
  have hh : W.a₁*u*v=0 := by rw [mul_assoc,huv,mul_zero]
  simp only [one_pow,one_mul,mul_one,hu2,hv2,hu3,hv3,hh,mul_zero,zero_mul,add_zero,sub_zero]

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

/-- Literal generalized J-model, arbitrary split square-zero test.
The first coordinate is genuinely unconstrained and the second is
forced zero; this is not yet construction of the global group scheme. -/
theorem literal_split_equation_iff (d : Rˣ) (u v : V) :
    ((SelectedGeneralizedJCurve318.curve d).baseChange (TrivSqZeroExt R V)).toProjective.Equation
      ![TrivSqZeroExt.inr u,1,TrivSqZeroExt.inr v] ↔ v = 0 := by
  rw [infinity_equation_iff _
    (TrivSqZeroExt.inr u) (TrivSqZeroExt.inr v)
    (TrivSqZeroExt.inr_mul_inr R u u) (TrivSqZeroExt.inr_mul_inr R v v)
    (TrivSqZeroExt.inr_mul_inr R u v)]
  constructor
  · intro h
    exact TrivSqZeroExt.inr_injective (h.trans TrivSqZeroExt.inr_zero.symm)
  · rintro rfl
    exact TrivSqZeroExt.inr_zero

end SelectedGeneralizedInfinityJets318

#print axioms SelectedGeneralizedInfinityJets318.infinity_equation_iff
#print axioms SelectedGeneralizedInfinityJets318.literal_split_equation_iff
