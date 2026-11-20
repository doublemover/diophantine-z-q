module
public import SelectedPrimitiveAffineSign318
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318

namespace SelectedPrimitiveFixedX318

variable (n : ℕ) (I : Ideal (D n))

abbrev q := Ideal.Quotient.mkₐ (R n) I
abbrev xbar : D n ⧸ I := q n I (SelectedPrimitiveAffineSign318.X n)
abbrev ybar : D n ⧸ I := q n I (SelectedPrimitiveAffineSign318.Y n)

private theorem short_equation :
    ybar n I ^ 2 = xbar n I ^ 3 + algebraMap (R n) (D n ⧸ I) (A n) * xbar n I +
      algebraMap (R n) (D n ⧸ I) (B n) := by
  have h := congrArg (q n I) (ShortAffineJacobian318.relation (A n) (B n))
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] at h
  linear_combination h

/-- Every element of the actual short quotient is p(x)+y r(x), without
requiring the quotient to be reduced or its coordinate module to be free. -/
theorem even_odd (b : D n ⧸ I) :
    ∃ p r : (R n)[X], b = aeval (xbar n I) p + ybar n I * aeval (xbar n I) r := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective b
  change ∃ p r : (R n)[X], q n I d = _
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective d
  let Q := q n I
  let ev := (aeval (xbar n I) : (R n)[X] →ₐ[R n] (D n ⧸ I))
  let f3 : (R n)[X] := Polynomial.X^3 + C (A n)*Polynomial.X + C (B n)
  have hf3 : ev f3 = ybar n I ^ 2 := by
    simpa only [f3,ev,map_add,map_pow,map_mul,aeval_X,aeval_C] using (short_equation n I).symm
  change ∃ p r : (R n)[X], Q (Ideal.Quotient.mk _ f) = ev p + ybar n I * ev r
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨C a,0,?_⟩
    rw [ShortAffineJacobian318.mk_C,Q.commutes,map_zero,mul_zero,add_zero]
    exact (aeval_C _ _).symm
  | add f g hf hg =>
    obtain ⟨p,r,hp⟩ := hf
    obtain ⟨p',r',hp'⟩ := hg
    refine ⟨p+p',r+r',?_⟩
    rw [map_add,map_add,hp,hp',map_add,map_add]
    ring
  | mul_X f i hf =>
    obtain ⟨p,r,h⟩ := hf
    have hX : ev Polynomial.X = xbar n I := aeval_X _
    fin_cases i
    · refine ⟨p*Polynomial.X,r*Polynomial.X,?_⟩
      rw [map_mul,map_mul,h]
      change (ev p + ybar n I * ev r) * xbar n I = _
      rw [map_mul,map_mul,hX]
      ring
    · refine ⟨r*f3,p,?_⟩
      rw [map_mul,map_mul,h]
      change (ev p + ybar n I * ev r) * ybar n I = _
      rw [map_mul,hf3]
      ring

section Fixed

variable (τ : (D n ⧸ I) →ₐ[R n] (D n ⧸ I))
variable (hτ : τ.comp (q n I) = (q n I).comp (sign n))

private theorem sign_x : τ (xbar n I) = xbar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_x] using
    congrArg (fun f : D n →ₐ[R n] (D n ⧸ I) => f (SelectedPrimitiveAffineSign318.X n)) hτ

private theorem sign_y : τ (ybar n I) = -ybar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using
    congrArg (fun f : D n →ₐ[R n] (D n ⧸ I) => f (SelectedPrimitiveAffineSign318.Y n)) hτ

private theorem sign_eval (p : (R n)[X]) :
    τ (aeval (xbar n I) p) = aeval (xbar n I) p := by
  have hh : τ.comp (aeval (xbar n I)) = aeval (xbar n I) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply,aeval_X] using sign_x n I τ hτ
  exact congrArg (fun f : (R n)[X] →ₐ[R n] (D n ⧸ I) => f p) hh

/-- The actual fixed elements are precisely polynomials in the genuine
affine x. The proof kills the odd part using the actual unit 2 of the base. -/
theorem fixed_iff_polynomial (b : D n ⧸ I) :
    τ b = b ↔ ∃ p : (R n)[X], aeval (xbar n I) p = b := by
  constructor
  · intro hb
    obtain ⟨p,r,he⟩ := even_odd n I b
    rw [he,map_add,map_mul,sign_eval n I τ hτ,sign_eval n I τ hτ,sign_y n I τ hτ] at hb
    have hz : (2 : D n ⧸ I) * (ybar n I * aeval (xbar n I) r) = 0 := by
      linear_combination -hb
    obtain ⟨u,hu⟩ : IsUnit (2 : D n ⧸ I) := by
      simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map
        (algebraMap (R n) (D n ⧸ I))
    have htwo : (↑u⁻¹ : D n ⧸ I) * 2 = 1 := by
      rw [← hu]
      exact Units.inv_mul u
    have ho : ybar n I * aeval (xbar n I) r = 0 := by
      rw [← one_mul (ybar n I * aeval (xbar n I) r),← htwo,mul_assoc,hz,mul_zero]
    exact ⟨p,by rw [he,ho,add_zero]⟩
  · rintro ⟨p,rfl⟩
    exact sign_eval n I τ hτ p

/-- The fixed algebra of the actual involution. -/
@[expose] def fixed : Subalgebra (R n) (D n ⧸ I) where
  carrier := {b | τ b = b}
  zero_mem' := map_zero τ
  one_mem' := map_one τ
  add_mem' ha hb := by rw [map_add,ha,hb]
  mul_mem' ha hb := by rw [map_mul,ha,hb]
  algebraMap_mem' := τ.commutes

theorem fixed_eq_eval_range :
    fixed n I τ = (aeval (xbar n I) : (R n)[X] →ₐ[R n] (D n ⧸ I)).range := by
  ext b
  exact fixed_iff_polynomial n I τ hτ b

/-- The actual unit 2 of the base gives a linear retraction onto the
fixed subalgebra; no flatness of a residue-field specialization is assumed. -/
theorem reynolds (hinv : τ.comp τ = AlgHom.id (R n) (D n ⧸ I)) :
    ∃ P : (D n ⧸ I) →ₗ[R n] (fixed n I τ),
      P.comp (fixed n I τ).val.toLinearMap = LinearMap.id := by
  let t := ((OpenJModel318.base_units n).1.unit⁻¹ : (R n)ˣ)
  let h := algebraMap (R n) (D n ⧸ I) (t : R n)
  have ht : (t : R n) * 2 = 1 := by
    change (↑((OpenJModel318.base_units n).1.unit⁻¹) : R n) * 2 = 1
    rw [← (OpenJModel318.base_units n).1.unit_spec]
    exact Units.inv_mul _
  have hh : h * 2 = 1 := by
    simpa only [map_mul,map_one,map_ofNat] using
      congrArg (algebraMap (R n) (D n ⧸ I)) ht
  have sq (b : D n ⧸ I) : τ (τ b) = b :=
    congrArg (fun f : (D n ⧸ I) →ₐ[R n] (D n ⧸ I) => f b) hinv
  let P : (D n ⧸ I) →ₗ[R n] (fixed n I τ) :=
    { toFun := fun b => ⟨h * (b + τ b),by
        change τ (h * (b + τ b)) = h * (b + τ b)
        rw [map_mul,τ.commutes,map_add,sq,add_comm (τ b) b]⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change h * (a+b+τ (a+b)) = h * (a+τ a) + h * (b+τ b)
        rw [map_add]
        ring
      map_smul' := fun r b => by
        apply Subtype.ext
        change h * (algebraMap (R n) (D n ⧸ I) r * b +
          τ (algebraMap (R n) (D n ⧸ I) r * b)) =
          algebraMap (R n) (D n ⧸ I) r * (h * (b + τ b))
        rw [map_mul,τ.commutes]
        ring }
  refine ⟨P,?_⟩
  ext b
  apply Subtype.ext
  change h * (b.val + τ b.val) = b.val
  rw [show τ b.val = b.val from b.property,← two_mul,← mul_assoc,hh,one_mul]

/-- Finiteness and flatness of the fixed algebra descend as a direct
summand of the actual finite étale coordinate algebra. -/
theorem finite_flat_fixed [Module.Finite (R n) (D n ⧸ I)]
    [Module.Flat (R n) (D n ⧸ I)]
    (hinv : τ.comp τ = AlgHom.id (R n) (D n ⧸ I)) :
    Module.Finite (R n) (fixed n I τ) ∧ Module.Flat (R n) (fixed n I τ) := by
  obtain ⟨P,hP⟩ := reynolds n I τ hinv
  refine ⟨Module.Finite.of_surjective P ?_,
    Module.Flat.of_retract (fixed n I τ).val.toLinearMap P hP⟩
  intro b
  exact ⟨b.val,DFunLike.congr_fun hP b⟩

end Fixed
end SelectedPrimitiveFixedX318

#print axioms SelectedPrimitiveFixedX318.fixed_eq_eval_range
#print axioms SelectedPrimitiveFixedX318.finite_flat_fixed
