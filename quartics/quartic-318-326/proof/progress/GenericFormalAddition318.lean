module
public import FormalChain318
public import GenericFormalDifferential318
public section
namespace GenericFormalAddition318
open MvPowerSeries
open scoped PowerSeries
variable {K : Type*} [Field K] [CharZero K]
abbrev S (K : Type*) := MvPowerSeries (Fin 2) K
@[expose] noncomputable def x : S K := X 0
@[expose] noncomputable def a : S K := X 1
@[expose] noncomputable def v (D : K) (g : S K) : S K := (GenericFormalDifferential318.branch D).subst g
@[expose] noncomputable def l (D : K) (g : S K) : S K := (GenericFormalDifferential318.integral D).subst g
@[expose] noncomputable def q (D : K) : S K := 1+C D*x^2*a^2
@[expose] noncomputable def n (D : K) : S K := x*v D a+a*v D x
@[expose] noncomputable def m (D : K) : S K :=
  v D x*v D a*(1-C D*x^2*a^2)-2*C D*x*a*(x^2+a^2)
@[expose] noncomputable def f (D : K) : S K := n D*(q D)⁻¹
@[expose] noncomputable def b (D : K) (g : S K) : S K := (GenericFormalDifferential318.differential D).subst g

@[simp] theorem x_zero : constantCoeff (x (K:=K))=0 := by simp [x]
@[simp] theorem a_zero : constantCoeff (a (K:=K))=0 := by simp [a]
@[simp] theorem q_zero (D : K) : constantCoeff (q D)=1 := by simp [q]
@[simp] theorem v_zero (D : K) (g : S K) (hg : constantCoeff g=0) : constantCoeff (v D g)=1 := by
  rw [v,PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg,
    GenericFormalDifferential318.branch_constant]
  rfl
@[simp] theorem n_zero (D : K) : constantCoeff (n D)=0 := by simp [n]
@[simp] theorem f_zero (D : K) : constantCoeff (f D)=0 := by simp [f]
@[simp] theorem m_zero (D : K) : constantCoeff (m D)=1 := by simp [m,v_zero]

theorem subst_nat (g : S K) (k : ℕ) : (k:PowerSeries K).subst g=k := by
  rw [←map_natCast PowerSeries.C,PowerSeries.subst_C]
  exact map_natCast C k

theorem v_square (D : K) (g : S K) (hg : constantCoeff g=0) : (v D g)^2=1-C D*g^4 := by
  have hs : PowerSeries.HasSubst g := .of_constantCoeff_zero hg
  have h := congrArg (fun z : PowerSeries K => z.subst g) (GenericFormalDifferential318.branch_square D)
  simpa only [PowerSeries.subst_pow hs,PowerSeries.subst_sub hs,
    GenericFormalDifferential318.argument,PowerSeries.subst_mul hs,PowerSeries.subst_C,
    PowerSeries.subst_X hs,show (1:PowerSeries K).subst g=1 from by simpa only [Nat.cast_one] using subst_nat g 1,v] using h

theorem b_v (D : K) (g : S K) (hg : constantCoeff g=0) : b D g*v D g=1 := by
  have hs : PowerSeries.HasSubst g := .of_constantCoeff_zero hg
  have h := congrArg (fun z : PowerSeries K => z.subst g) (GenericFormalDifferential318.differential_branch D)
  simpa only [PowerSeries.subst_mul hs,show (1:PowerSeries K).subst g=1 from by simpa only [Nat.cast_one] using subst_nat g 1,b,v] using h

theorem l_deriv (D : K) (g : S K) (hg : constantCoeff g=0) (i : Fin 2) :
    pderiv i (l D g)=-b D g*pderiv i g := by
  rw [l,FormalChain318.chain i _ g hg,GenericFormalDifferential318.integral_derivative,
    ←PowerSeries.coe_substAlgHom (.of_constantCoeff_zero hg),map_neg,PowerSeries.coe_substAlgHom]
  rfl

theorem q_inverse (D : K) : q D*(q D)⁻¹=1 :=
  MvPowerSeries.mul_inv_cancel _ (by rw [q_zero]; norm_num)

/-- Polynomial identity underlying the lemniscatic addition formula. -/
theorem addition_curve_polynomial {R : Type*} [CommRing R] (D x y a b : R)
    (hy : y^2=1-D*x^4) (hb : b^2=1-D*a^4) :
    (y*b*(1-D*x^2*a^2)-2*D*x*a*(x^2+a^2))^2 =
      (1+D*x^2*a^2)^4-D*(x*b+a*y)^4 := by
  linear_combination
    (D^2*a^4*b^2*x^4-D^2*a^4*x^4+D*a^4*y^2+D*a^4+4*D*a^3*b*x*y+4*D*a^2*b^2*x^2+b^2)*hy +
    (-D^3*a^4*x^8-4*D^2*a^2*x^6+4*D*a^2*x^2+4*D*a*b*x^3*y+D*b^2*x^4+1)*hb

theorem m_square (D : K) : (m D)^2=(q D)^4-C D*(n D)^4 :=
  addition_curve_polynomial (C D) x (v D x) a (v D a) (v_square D x x_zero) (v_square D a a_zero)

theorem f_curve (D : K) : (m D*(q D)⁻¹^2)^2=1-C D*(f D)^4 := by
  have hq := congrArg (fun z : S K => z^4) (q_inverse D)
  simp only [mul_pow,one_pow] at hq
  dsimp only [f]
  rw [mul_pow,m_square]
  linear_combination hq

theorem f_branch (D : K) : v D (f D)=m D*(q D)⁻¹^2 := by
  have h1 := v_square D (f D) (f_zero D)
  have h2 := f_curve D
  have he : (v D (f D)-m D*(q D)⁻¹^2)*(v D (f D)+m D*(q D)⁻¹^2)=0 := by
    linear_combination h1-h2
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp he).resolve_right
  intro hz
  have hc := congrArg constantCoeff hz
  norm_num [v_zero,m_zero,q_zero] at hc


theorem v_deriv (D : K) (g : S K) (hg : constantCoeff g=0) (i : Fin 2) :
    pderiv i (v D g)*v D g=-2*C D*g^3*pderiv i g := by
  have hh := congrArg (pderiv i) (v_square D g hg)
  simp only [pderiv_pow,map_sub,pderiv_one,Derivation.leibniz,pderiv_C] at hh
  norm_num at hh
  have hz : (2:S K)*(pderiv i (v D g)*v D g+2*C D*g^3*pderiv i g)=0 := by
    linear_combination hh
  have he := (mul_eq_zero.mp hz).resolve_left (by intro h; have hc := congrArg constantCoeff h; change (2:K)=0 at hc; norm_num at hc : (2:S K)≠0)
  linear_combination he

@[simp] theorem dx : pderiv (0:Fin 2) (x (K:=K))=1 := by simp [x,pderiv_X]
@[simp] theorem da : pderiv (0:Fin 2) (a (K:=K))=0 := by simp [a,pderiv_X]
@[simp] theorem ax : pderiv (1:Fin 2) (x (K:=K))=0 := by simp [x,pderiv_X]
@[simp] theorem aa : pderiv (1:Fin 2) (a (K:=K))=1 := by simp [a,pderiv_X]
@[simp] theorem v_a_dx (D : K) : pderiv (0:Fin 2) (v D a)=0 := by
  rw [v,FormalChain318.chain _ _ _ a_zero,da,mul_zero]
@[simp] theorem v_x_da (D : K) : pderiv (1:Fin 2) (v D x)=0 := by
  rw [v,FormalChain318.chain _ _ _ x_zero,ax,mul_zero]

theorem f_dx (D : K) : pderiv (0:Fin 2) (f D)*v D x=m D*(q D)⁻¹^2 := by
  have hv := v_deriv D x x_zero (0:Fin 2)
  simp only [dx,mul_one] at hv
  have hc := v_square D x x_zero
  have hq := q_inverse D
  simp only [f,n,Derivation.leibniz,map_add,dx,da,one_mul,zero_mul,mul_zero,
    v_a_dx,add_zero,zero_add,pderiv_inv']
  have hdq : pderiv (0:Fin 2) (q D)=2*C D*x*a^2 := by
    simp only [q,map_add,pderiv_one,Derivation.leibniz,pderiv_C,pderiv_pow,dx,da]
    norm_num
    ring
  rw [hdq]
  dsimp only [m,q] at hq ⊢
  linear_combination
    a*(1+C D*x^2*a^2)⁻¹*hv -
    2*C D*x*a^3*((1+C D*x^2*a^2)⁻¹)^2*hc +
    (2*C D*x^3*a-v D a*v D x)*(1+C D*x^2*a^2)⁻¹*hq



theorem f_da (D : K) : pderiv (1:Fin 2) (f D)*v D a=m D*(q D)⁻¹^2 := by
  have hv := v_deriv D a a_zero (1:Fin 2)
  simp only [aa,mul_one] at hv
  have hc := v_square D a a_zero
  have hq := q_inverse D
  simp only [f,n,Derivation.leibniz,map_add,ax,aa,one_mul,zero_mul,mul_zero,
    v_x_da,add_zero,zero_add,pderiv_inv']
  have hdq : pderiv (1:Fin 2) (q D)=2*C D*x^2*a := by
    simp only [q,map_add,pderiv_one,Derivation.leibniz,pderiv_C,pderiv_pow,ax,aa]
    norm_num
    ring
  rw [hdq]
  dsimp only [m,q] at hq ⊢
  linear_combination
    x*(1+C D*x^2*a^2)⁻¹*hv -
    2*C D*a*x^3*((1+C D*x^2*a^2)⁻¹)^2*hc +
    (2*C D*a^3*x-v D x*v D a)*(1+C D*x^2*a^2)⁻¹*hq

theorem v_ne_zero (D : K) (g : S K) (hg : constantCoeff g=0) : v D g≠0 := by
  intro hz
  have h := b_v D g hg
  simp only [hz,mul_zero] at h
  exact zero_ne_one h

theorem l_constant (D : K) (g : S K) (hg : constantCoeff g=0) : constantCoeff (l D g)=0 := by
  rw [l,PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg,GenericFormalDifferential318.integral_constant]
  rfl

/-- The full, untruncated reciprocal formal integral is additive for the
lemniscatic formal addition law. -/
theorem formal_addition (D : K) : l D (f D)=l D x+l D a := by
  apply MvPowerSeries.pderiv.ext
  · intro i
    fin_cases i
    · change pderiv (0:Fin 2) (l D (f D))=pderiv (0:Fin 2) (l D x+l D a)
      rw [l_deriv D (f D) (f_zero D),map_add,l_deriv D x x_zero,l_deriv D a a_zero,
        dx,da,mul_one,mul_zero,add_zero]
      apply mul_right_cancel₀ (v_ne_zero D x x_zero)
      calc
        (-b D (f D)*pderiv (0:Fin 2) (f D))*v D x =
          -b D (f D)*(pderiv (0:Fin 2) (f D)*v D x) := by ring
        _ = -b D (f D)*v D (f D) := by rw [f_dx,←f_branch]
        _ = -1 := by rw [neg_mul,b_v D (f D) (f_zero D)]
        _ = (-b D x)*v D x := by rw [neg_mul,b_v D x x_zero]
    · change pderiv (1:Fin 2) (l D (f D))=pderiv (1:Fin 2) (l D x+l D a)
      rw [l_deriv D (f D) (f_zero D),map_add,l_deriv D x x_zero,l_deriv D a a_zero,
        ax,aa,mul_one,mul_zero,zero_add]
      apply mul_right_cancel₀ (v_ne_zero D a a_zero)
      calc
        (-b D (f D)*pderiv (1:Fin 2) (f D))*v D a =
          -b D (f D)*(pderiv (1:Fin 2) (f D)*v D a) := by ring
        _ = -b D (f D)*v D (f D) := by rw [f_da,←f_branch]
        _ = -1 := by rw [neg_mul,b_v D (f D) (f_zero D)]
        _ = (-b D a)*v D a := by rw [neg_mul,b_v D a a_zero]
  · rw [map_add,l_constant D (f D) (f_zero D),l_constant D x x_zero,l_constant D a a_zero,add_zero]


end GenericFormalAddition318
#print axioms GenericFormalAddition318.f_branch

#print axioms GenericFormalAddition318.f_dx

#print axioms GenericFormalAddition318.formal_addition
