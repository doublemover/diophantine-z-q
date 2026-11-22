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

private abbrev coeff : R n →+* (D n ⧸ I) :=
  (q n I).toRingHom.comp (algebraMap (R n) (D n))

private theorem short_equation :
    ybar n I ^ 2 = xbar n I ^ 3 + coeff n I (A n) * xbar n I + coeff n I (B n) := by
  have h := congrArg (q n I) (ShortAffineJacobian318.relation (A n) (B n))
  simp only [map_sub,map_pow,map_mul,map_zero] at h
  linear_combination h

private theorem add_mapped_zero {P C : Type*} [CommRing P] [CommRing C]
    (e : P →+* C) (y a : C) :
    a = a + y * e 0 := by rw [map_zero,mul_zero,add_zero]

/-- Every element of the actual short quotient is p(x)+y r(x), without
requiring the quotient to be reduced or its coordinate module to be free. -/
theorem even_odd (b : D n ⧸ I) :
    ∃ p r : (R n)[X], b = aeval (xbar n I) p + ybar n I * aeval (xbar n I) r := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective b
  change ∃ p r : (R n)[X], q n I d = _
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective d
  let Q := q n I
  let ev : (R n)[X] →ₐ[R n] (D n ⧸ I) := aeval (xbar n I)
  let f3 : (R n)[X] := Polynomial.X^3 + C (A n)*Polynomial.X + C (B n)
  have hevC (a : R n) : ev (C a) = coeff n I a := by
    change aeval (xbar n I) (C a) = Q (algebraMap (R n) (D n) a)
    exact (aeval_C (xbar n I) a).trans (Q.commutes a).symm
  have hevX : ev Polynomial.X = xbar n I := aeval_X _
  have hf3 : ev f3 = ybar n I ^ 2 := by
    change ev (Polynomial.X^3 + C (A n)*Polynomial.X + C (B n)) = _
    rw [map_add,map_add,map_mul,map_pow,hevX,hevC,hevC]
    exact (short_equation n I).symm
  change ∃ p r : (R n)[X], Q (Ideal.Quotient.mk _ f) = ev p + ybar n I * ev r
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨C a,0,?_⟩
    calc
      Q (Ideal.Quotient.mk _ (MvPolynomial.C a)) = coeff n I a := by
        rw [ShortAffineJacobian318.mk_C] <;> rfl
      _ = ev (C a) := (hevC a).symm
      _ = ev (C a) + ybar n I * ev 0 :=
        add_mapped_zero ev.toRingHom (ybar n I) (ev (C a))
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

include hτ in
private theorem sign_x : τ (xbar n I) = xbar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_x] using
    congrArg (fun f : D n →ₐ[R n] (D n ⧸ I) => f (SelectedPrimitiveAffineSign318.X n)) hτ

include hτ in
private theorem sign_y : τ (ybar n I) = -ybar n I := by
  simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using
    congrArg (fun f : D n →ₐ[R n] (D n ⧸ I) => f (SelectedPrimitiveAffineSign318.Y n)) hτ

include hτ in
private theorem sign_eval (p : (R n)[X]) :
    τ (aeval (xbar n I) p) = aeval (xbar n I) p := by
  have hh : τ.comp (aeval (xbar n I)) = aeval (xbar n I) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply,aeval_X] using sign_x n I τ hτ
  exact congrArg (fun f : (R n)[X] →ₐ[R n] (D n ⧸ I) => f p) hh

include hτ in
/-- The actual fixed elements are precisely polynomials in the genuine
affine x. The proof kills the odd part using the actual unit 2 of the base. -/
theorem fixed_iff_polynomial (b : D n ⧸ I) :
    τ b = b ↔ ∃ p : (R n)[X], aeval (xbar n I) p = b := by
  constructor
  · intro hb
    obtain ⟨p,r,he⟩ := even_odd n I b
    simp only [he,map_add,map_mul,sign_eval n I τ hτ,sign_y n I τ hτ] at hb
    have hz : (2 : D n ⧸ I) * (ybar n I * aeval (xbar n I) r) = 0 := by
      linear_combination -hb
    have hu : IsUnit (2 : D n ⧸ I) := by
      have hv : IsUnit (coeff n I (2 : R n)) :=
        (OpenJModel318.base_units n).1.map (coeff n I)
      simpa only [map_ofNat] using hv
    have ho : ybar n I * aeval (xbar n I) r = 0 :=
      hu.mul_left_cancel (hz.trans (mul_zero (2 : D n ⧸ I)).symm)
    exact ⟨p,by rw [he,ho,add_zero]⟩
  · rintro ⟨p,rfl⟩
    exact sign_eval n I τ hτ p

/-- The fixed algebra of the actual involution. -/
@[expose] def fixed : Subalgebra (R n) (D n ⧸ I) where
  carrier := {b | τ b = b}
  zero_mem' := map_zero τ
  one_mem' := map_one τ
  add_mem' := by
    intro a b ha hb
    change τ a = a at ha
    change τ b = b at hb
    change τ (a+b) = a+b
    rw [map_add,ha,hb]
  mul_mem' := by
    intro a b ha hb
    change τ a = a at ha
    change τ b = b at hb
    change τ (a*b) = a*b
    rw [map_mul,ha,hb]
  algebraMap_mem' := τ.commutes

include hτ in
theorem fixed_eq_eval_range :
    fixed n I τ = (aeval (xbar n I) : (R n)[X] →ₐ[R n] (D n ⧸ I)).range := by
  ext b
  exact fixed_iff_polynomial n I τ hτ b

/-- Work at an abstract algebra so the linearity proof does not
normalize the two nested literal curve quotient rings. -/
private theorem reynolds_of {S E : Type*} [CommRing S] [CommRing E] [Algebra S E]
    (T : Subalgebra S E) (σ : E →ₐ[S] E) (hT : ∀ a : E, a∈T ↔ σ a=a)
    (hinv : ∀ a : E, σ (σ a)=a) (h : E) (hfix : σ h=h) (hhalf : h*2=1) :
    ∃ P : E →ₗ[S] T, P.comp T.val.toLinearMap = LinearMap.id := by
  have hlinear (r : S) (b : E) :
      h * (r • b + σ (r • b)) = r • (h * (b + σ b)) := by
    simp only [Algebra.smul_def,map_mul,σ.commutes]
    ring
  let P : E →ₗ[S] T :=
    { toFun := fun b => ⟨h * (b + σ b),(hT _).2 (by
        rw [map_mul,hfix,map_add,hinv,add_comm (σ b) b])⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change h * (a+b+σ (a+b)) = h * (a+σ a) + h * (b+σ b)
        rw [map_add]
        ring
      map_smul' := fun r b => by
        apply Subtype.ext
        change h * (r • b + σ (r • b)) = r • (h * (b + σ b))
        exact hlinear r b }
  refine ⟨P,?_⟩
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change h * (b.val + σ b.val) = b.val
  rw [(hT _).1 b.property,← two_mul,← mul_assoc,hhalf,one_mul]

/-- The actual unit 2 of the base gives a linear retraction onto the
fixed subalgebra; no flatness of a residue-field specialization is assumed. -/
theorem reynolds (hinv : τ.comp τ = AlgHom.id (R n) (D n ⧸ I)) :
    ∃ P : (D n ⧸ I) →ₗ[R n] (fixed n I τ),
      P.comp (fixed n I τ).val.toLinearMap = LinearMap.id := by
  let u : (R n)ˣ := (OpenJModel318.base_units n).1.unit
  let t : (R n)ˣ := u⁻¹
  let h : D n ⧸ I := coeff n I (t : R n)
  have hu : (u : R n) = 2 := (OpenJModel318.base_units n).1.unit_spec
  have ht : (t : R n) * 2 = 1 := by
    calc
      (t : R n)*2 = (t : R n)*(u : R n) :=
        congrArg (fun c : R n => (t : R n)*c) hu.symm
      _ = 1 := Units.inv_mul u
  have hh : h * 2 = 1 := by
    simpa only [map_mul,map_one,map_ofNat] using congrArg (coeff n I) ht
  have hfixed : τ h = h := τ.commutes (t : R n)
  have sq (b : D n ⧸ I) : τ (τ b) = b :=
    congrArg (fun f : (D n ⧸ I) →ₐ[R n] (D n ⧸ I) => f b) hinv
  exact reynolds_of (fixed n I τ) τ (fun _ => Iff.rfl) sq h hfixed hh

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
