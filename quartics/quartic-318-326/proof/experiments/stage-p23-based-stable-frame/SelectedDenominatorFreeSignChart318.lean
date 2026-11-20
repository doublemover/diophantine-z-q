module
public import SelectedNormalizedEtaleDJ318
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic
public section
noncomputable section
open Polynomial

namespace SelectedDenominatorFreeSignChart318

section LiteralLevel
variable {S e d : ℕ}

/-- A retained prime-to-2 part cannot lose the fixed factor 3⁶ of
the original literal level, independently of S. -/
theorem odd_order (hS : 0 < S) (h : 2^28*3^6*S^2 = 2^e*d) :
    3^6 ∣ d ∧ 2 < d := by
  have hc : Nat.Coprime (3^6) (2^e) :=
    Nat.coprime_pow_primes 6 e (by decide) (by decide) (by decide)
  have hd : 3^6 ∣ d := hc.dvd_of_dvd_mul_left (by
    rw [← h]
    exact ⟨2^28*S^2,by ring⟩)
  have hpos : 0 < d := by
    by_contra! hn
    have hz : d = 0 := by omega
    rw [hz,mul_zero] at h
    exact (show 0 < (2:ℕ)^28*3^6*S^2 by positivity).ne' h
  exact ⟨hd,(by decide : 2 < (3:ℕ)^6).trans_le (Nat.le_of_dvd hpos hd)⟩

/-- A retained prime-to-3 part similarly keeps the fixed factor 2²⁸. -/
theorem prime_to_three_order (hS : 0 < S) (h : 2^28*3^6*S^2 = 3^e*d) :
    2^28 ∣ d ∧ 2 < d := by
  have hc : Nat.Coprime (2^28) (3^e) :=
    Nat.coprime_pow_primes 28 e (by decide) (by decide) (by decide)
  have hd : 2^28 ∣ d := hc.dvd_of_dvd_mul_left (by
    rw [← h]
    exact ⟨3^6*S^2,by ring⟩)
  have hpos : 0 < d := by
    by_contra! hn
    have hz : d = 0 := by omega
    rw [hz,mul_zero] at h
    exact (show 0 < (2:ℕ)^28*3^6*S^2 by positivity).ne' h
  exact ⟨hd,(by decide : 2 < (2:ℕ)^28).trans_le (Nat.le_of_dvd hpos hd)⟩

end LiteralLevel

section Quadratic
variable {R : Type*} [CommRing R]

/-- The actual affine Weierstrass equation in the ordinate, with
b=a₁x+a₃ and f=x³+a₂x²+a₄x+a₆ in the base. -/
@[expose] def equation (b f : R) : R[X] := X^2 + (C b*X + C (-f))
@[expose] def discriminant (b f : R) : R := b^2+4*f

private theorem tail_degree (b f : R) :
    (C b*X + C (-f) : R[X]).degree < 2 := by
  have h : (C b*X + C (-f) : R[X]).degree ≤ 1 :=
    Polynomial.degree_add_le_of_degree_le (Polynomial.degree_C_mul_X_le b)
      (Polynomial.degree_C_le.trans (by norm_num))
  exact h.trans_lt (by norm_num)

theorem monic (b f : R) : (equation b f).Monic :=
  Polynomial.monic_X_pow_add (tail_degree b f)

abbrev RootRing (b f : R) := AdjoinRoot (equation b f)
@[expose] def ordinate (b f : R) : RootRing b f := AdjoinRoot.root (equation b f)

theorem ordinate_equation (b f : R) :
    (ordinate b f)^2+algebraMap R (RootRing b f) b*ordinate b f =
      algebraMap R (RootRing b f) f := by
  have h := AdjoinRoot.eval₂_root (equation b f)
  change (equation b f).eval₂ (algebraMap R (RootRing b f)) (ordinate b f) = 0 at h
  simp only [equation,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,map_neg] at h
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg,add_assoc] using h

theorem derivative_equation (b f : R) :
    (equation b f).derivative = C (2:R)*X+C b := by
  simp only [equation,derivative_add,derivative_X_sq,derivative_C_mul_X,derivative_C,add_zero]

theorem derivative_ordinate (b f : R) :
    AdjoinRoot.mk (equation b f) (equation b f).derivative =
      2*ordinate b f+algebraMap R (RootRing b f) b := by
  rw [derivative_equation,map_add,map_mul,AdjoinRoot.mk_C,AdjoinRoot.mk_X,AdjoinRoot.mk_C]
  change (AdjoinRoot.of (equation b f)) 2*ordinate b f+_ = _
  rw [map_ofNat]

/-- Full discriminant identity, valid also when 2 vanishes. -/
theorem derivative_square (b f : R) :
    (AdjoinRoot.mk (equation b f) (equation b f).derivative)^2 =
      algebraMap R (RootRing b f) (discriminant b f) := by
  rw [derivative_ordinate]
  simp only [discriminant,map_add,map_pow,map_mul,map_ofNat]
  calc
    _ = (algebraMap R (RootRing b f) b)^2 +
        4*((ordinate b f)^2+algebraMap R (RootRing b f) b*ordinate b f) := by ring
    _ = _ := by rw [ordinate_equation]

/-- The actual quadratic ordinate chart is finite étale over the
x-line wherever its discriminant is a unit. There is NO IsUnit 2
premise: in residue characteristic 2 the linear term may suffice. -/
theorem finite_etale (b f : R) (h : IsUnit (discriminant b f)) :
    Module.Finite R (RootRing b f) ∧ Algebra.Etale R (RootRing b f) := by
  refine ⟨(monic b f).finite_adjoinRoot,?_⟩
  apply SelectedNormalizedEtaleDJ318.etale_of_derivative _ (monic b f)
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [derivative_square]
  exact h.map (algebraMap R (RootRing b f))

theorem faithfullyFlat [Nontrivial R] (b f : R) : Module.FaithfullyFlat R (RootRing b f) := by
  letI : Nontrivial (RootRing b f) := by
    apply (AdjoinRoot.nontrivial_iff_of_monic (monic b f)).mpr
    have hd : (X^2 : R[X]).degree = 2 := Polynomial.degree_X_pow 2
    have ht : (C b*X+C (-f) : R[X]).degree < (X^2 : R[X]).degree := by
      rw [hd]
      exact tail_degree b f
    rw [equation,Polynomial.degree_add_eq_left_of_degree_lt ht,hd]
    norm_num
  letI : Module.Free R (RootRing b f) := (monic b f).free_adjoinRoot
  infer_instance

/-- Fixed points of actual Weierstrass negation in the affine chart
are exactly the derivative-zero points, in EVERY characteristic. -/
theorem fixed_iff (b y : R) : -y-b = y ↔ 2*y+b = 0 := by
  constructor <;> intro h <;> linear_combination -h

/-- The two roots after base change to the true selected ordinate,
not a newly chosen square root. Their difference is the derivative. -/
theorem two_roots {b f y : R} (h : y^2+b*y=f) :
    equation b f = (X-C y)*(X-C (-y-b)) := by
  rw [equation,← h]
  simp only [map_neg,map_sub,map_add,map_mul,map_pow]
  ring

theorem coprime_roots (b y : R) (hu : IsUnit (2*y+b)) :
    IsCoprime (X-C y : R[X]) (X-C (-y-b)) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨-C (↑e⁻¹:R),C (↑e⁻¹:R),?_⟩
  calc
    _ = C (↑e⁻¹:R) * C (2*y+b) := by
      simp only [map_add,map_sub,map_neg,map_mul,map_ofNat]
      ring
    _ = 1 := by rw [←map_mul,← he,Units.inv_mul,map_one]

end Quadratic

section LiteralJModel
variable {R : Type*} [CommRing R]

/-- The coefficient in the exact denominator-free pinned model,
not the previously used short chart with 2 and 3 inverted. -/
theorem actual_linear (J x : R) :
    (WeierstrassCurve.ofJNe0Or1728 J).a₁*x+
      (WeierstrassCurve.ofJNe0Or1728 J).a₃ = (J-1728)*x := by
  simp [WeierstrassCurve.ofJNe0Or1728]

theorem actual_char_two_derivative (J x y : R) (h2 : (2:R)=0) :
    2*y+((WeierstrassCurve.ofJNe0Or1728 J).a₁*x+
      (WeierstrassCurve.ofJNe0Or1728 J).a₃) = (J-1728)*x := by
  rw [h2,zero_mul,zero_add,actual_linear]

/-- The true affine x-line coefficients of the denominator-free
model before localization in the sign discriminant. -/
@[expose] def linearX (J : R) : R[X] := C (J-1728)*X
@[expose] def cubicX (J : R) : R[X] := X^3-C (36*(J-1728)^3)*X-C ((J-1728)^5)

theorem actual_x_line (J : R) :
    C (WeierstrassCurve.ofJNe0Or1728 J).a₁*X+C (WeierstrassCurve.ofJNe0Or1728 J).a₃ =
      linearX J ∧
    X^3+C (WeierstrassCurve.ofJNe0Or1728 J).a₂*X^2+
      C (WeierstrassCurve.ofJNe0Or1728 J).a₄*X+C (WeierstrassCurve.ofJNe0Or1728 J).a₆ =
      cubicX J := by
  constructor
  · simp [linearX,WeierstrassCurve.ofJNe0Or1728]
  · simp [cubicX,WeierstrassCurve.ofJNe0Or1728,map_neg,sub_eq_add_neg,neg_mul]

abbrev XOpen (J : R) := Localization.Away (discriminant (linearX J) (cubicX J))
abbrev JSignChart (J : R) :=
  RootRing (algebraMap R[X] (XOpen J) (linearX J)) (algebraMap R[X] (XOpen J) (cubicX J))

/-- The literal x-line localization with its true monic ordinate
chart, not an assertion about the primitive closure or quotient. -/
theorem actual_chart_finite_etale (J : R) :
    Module.Finite (XOpen J) (JSignChart J) ∧ Algebra.Etale (XOpen J) (JSignChart J) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S:=XOpen J)
    (discriminant (linearX J) (cubicX J))
  exact finite_etale _ _ (by
    simpa only [discriminant,map_add,map_pow,map_mul,map_ofNat] using h)

end LiteralJModel
end SelectedDenominatorFreeSignChart318

#print axioms SelectedDenominatorFreeSignChart318.odd_order
#print axioms SelectedDenominatorFreeSignChart318.prime_to_three_order
#print axioms SelectedDenominatorFreeSignChart318.finite_etale
#print axioms SelectedDenominatorFreeSignChart318.faithfullyFlat
#print axioms SelectedDenominatorFreeSignChart318.coprime_roots
#print axioms SelectedDenominatorFreeSignChart318.actual_char_two_derivative
#print axioms SelectedDenominatorFreeSignChart318.actual_chart_finite_etale
