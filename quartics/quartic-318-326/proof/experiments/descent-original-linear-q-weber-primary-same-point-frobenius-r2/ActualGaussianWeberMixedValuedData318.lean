module
public import ActualGaussianWeberMixedPolynomial318
public import Mathlib.RingTheory.Valuation.ValuationSubring
public section
noncomputable section

namespace ActualGaussianWeberMixedValuedData318

open IsLocalRing
open ActualGaussianWeberHenselianChart318 ActualGaussianWeberMixedPolynomial318

variable {F : Type*} [Field F] (V : ValuationSubring F)

/-- An actual inverse in the valuation subring, reducing to 1. -/
theorem inverse_over_residue_one (x : V) (hx : residue V x=1) :
    ∃ u : V, x*u=1 ∧ residue V u=1 := by
  have hU : IsUnit x := (residue_ne_zero_iff_isUnit x).mp
    (fun h => one_ne_zero (hx.symm.trans h))
  obtain ⟨e,he⟩ := hU
  have h₁ : x*(↑e⁻¹:V)=1 := by rw [←he,e.mul_inv]
  exact ⟨↑e⁻¹,h₁,by simpa only [map_mul,map_one,hx,one_mul] using congrArg (residue V) h₁⟩

/-- Every quantity here is in the SAME valuation subring. The
original mixed slope itself need not be integral. -/
structure IntegralData (t w A B : V) where
  u : V
  beta : V
  X : V
  Y : V
  u_inv : (1+t*w)*u=1
  beta_inv : (1-A*t^2*u)*beta=1
  u_res : residue V u=1
  beta_res : residue V beta=1
  w_relation : w=t^3*u
  denominator : (t-A*w)*beta=t
  x_formula : X=A+t*u*beta^2*H t w A B
  y_formula : Y= -B+(1+B*w)*u*beta^3*H t w A B
  x_residue : residue V X=residue V A
  y_residue : residue V Y=residue V B

/-- Candidate actual integral coordinates; no reduction of
(1+Bw)/(t−Aw) is taken, so the zero residue denominator causes no issue. -/
theorem integral_data {t w : V} (A B : V) (ht : t∈maximalIdeal V)
    (hw : w∈maximalIdeal V) (hC : identityChart t w) :
    Nonempty (IntegralData V t w A B) := by
  have ht0 := (residue_eq_zero_iff t).mpr ht
  have hw0 := (residue_eq_zero_iff w).mpr hw
  have hu1 : residue V (1+t*w)=1 := by
    simp only [map_add,map_one,map_mul,ht0,zero_mul,add_zero]
  obtain ⟨u,hu,hur⟩ := inverse_over_residue_one V _ hu1
  have hB1 : residue V (1-A*t^2*u)=1 := by
    simp only [map_sub,map_mul,map_pow,map_one,ht0,zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero,zero_mul,sub_zero]
  obtain ⟨beta,hb,hbr⟩ := inverse_over_residue_one V _ hB1
  have hW0 : w*(1+t*w)=t^3 := by
    unfold identityChart at hC
    linear_combination hC
  have hW : w=t^3*u := by
    calc
      w = w*1 := (mul_one _).symm
      _ = w*((1+t*w)*u) := by rw [hu]
      _ = _ := by rw [←mul_assoc,hW0]
  have hD0 : t-A*w=t*(1-A*t^2*u) := by
    linear_combination -A*hW
  have hD : (t-A*w)*beta=t := by rw [hD0,mul_assoc,hb,mul_one]
  have hHr : residue V (H t w A B) = 2*residue V B := by
    simp only [H,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,ht0,hw0,mul_zero,add_zero,sub_zero]
  let X := A+t*u*beta^2*H t w A B
  let Y := -B+(1+B*w)*u*beta^3*H t w A B
  refine ⟨⟨u,beta,X,Y,hu,hb,hur,hbr,hW,hD,rfl,rfl,?_,?_⟩⟩
  · simp only [X,map_add,map_mul,ht0,zero_mul,add_zero]
  · simp only [Y,map_add,map_neg,map_mul,map_one,map_pow,hw0,hur,hbr,hHr,
      mul_zero,add_zero,one_mul,one_pow] <;> ring

end ActualGaussianWeberMixedValuedData318
