module
public import ActualSmallCoefficientPrimeBudget318
public section
noncomputable section
namespace ActualTZTwoBlockCoefficients318

open scoped BigOperators
open ActualSmallCoefficientPrimeBudget318

/-- Ordinary integer quadratic coefficient table. Only upper triangle
entries are read: a bilinear cross coefficient is not split in half and
no spurious antisymmetric coefficient can be marked. -/
structure Quadratic (n : ℕ) where
  constTerm : ℤ
  linear : Fin n → ℤ
  quadratic : Fin n → Fin n → ℤ

def qCoeff {n : ℕ} (Q : Quadratic n) (i j : Fin n) : ℤ :=
  if i≤j then Q.quadratic i j else 0

def bilinear {n : ℕ} (Q : Quadratic n) (x t : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n,∑ j : Fin n,qCoeff Q i j*x i*t j

def eval {n : ℕ} (Q : Quadratic n) (x : Fin n → ℤ) : ℤ :=
  Q.constTerm+(∑ i : Fin n,Q.linear i*x i)+bilinear Q x x

theorem bilinear_add_left {n : ℕ} (Q : Quadratic n) (x s t : Fin n → ℤ) :
    bilinear Q (x+s) t=bilinear Q x t+bilinear Q s t := by
  simp only [bilinear,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem bilinear_add_right {n : ℕ} (Q : Quadratic n) (x s t : Fin n → ℤ) :
    bilinear Q x (s+t)=bilinear Q x s+bilinear Q x t := by
  simp only [bilinear,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem bilinear_factor_left {n : ℕ} (Q : Quadratic n) (x s : Fin n → ℤ) :
    bilinear Q x s=∑ i : Fin n,(∑ j : Fin n,qCoeff Q i j*s j)*x i := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bilinear_factor_right {n : ℕ} (Q : Quadratic n) (x s : Fin n → ℤ) :
    bilinear Q s x=∑ i : Fin n,(∑ j : Fin n,qCoeff Q j i*s j)*x i := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]

/-- Ordinary translation by s, followed by subtracting an arbitrary
constant (the actual wrap may depend on the point/prime; it never
becomes a polynomial coefficient of positive degree in the cell). -/
def translated {n : ℕ} (Q : Quadratic n) (s : Fin n → ℤ) (wrap : ℤ) : Quadratic n where
  constTerm := eval Q s-wrap
  linear i := Q.linear i+
    (∑ j : Fin n,qCoeff Q i j*s j)+(∑ j : Fin n,qCoeff Q j i*s j)
  quadratic := Q.quadratic

theorem qCoeff_translated {n : ℕ} (Q : Quadratic n) (s : Fin n → ℤ) (wrap : ℤ)
    (i j : Fin n) : qCoeff (translated Q s wrap) i j=qCoeff Q i j := by
  simp only [qCoeff,translated]

theorem bilinear_translated {n : ℕ} (Q : Quadratic n) (s : Fin n → ℤ) (wrap : ℤ)
    (x t : Fin n → ℤ) : bilinear (translated Q s wrap) x t=bilinear Q x t := by
  simp only [bilinear,qCoeff_translated]

theorem eval_translated {n : ℕ} (Q : Quadratic n) (s : Fin n → ℤ) (wrap : ℤ)
    (x : Fin n → ℤ) : eval (translated Q s wrap) x=eval Q (x+s)-wrap := by
  have hb := bilinear_translated Q s wrap x x
  change (eval Q s-wrap)+
      (∑ i : Fin n,(Q.linear i+(∑ j : Fin n,qCoeff Q i j*s j)+
        (∑ j : Fin n,qCoeff Q j i*s j))*x i)+
      bilinear (translated Q s wrap) x x =
    Q.constTerm+(∑ i : Fin n,Q.linear i*(x+s) i)+bilinear Q (x+s) (x+s)-wrap
  rw [hb,bilinear_add_left Q x s (x+s),bilinear_add_right Q x x s,
    bilinear_add_right Q s x s]
  simp only [eval,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib,
    ←bilinear_factor_left Q x s,←bilinear_factor_right Q x s]
  ring

def physicalDifference {n : ℕ} (P Q : Quadratic n) (W b₁ b₂ : ℤ) : Quadratic n where
  constTerm := W*(P.constTerm-Q.constTerm)+(b₁-b₂)
  linear i := W*(P.linear i-Q.linear i)
  quadratic i j := W*(P.quadratic i j-Q.quadratic i j)

theorem physical_qCoeff {n : ℕ} (P Q : Quadratic n) (W b₁ b₂ : ℤ) (i j : Fin n) :
    qCoeff (physicalDifference P Q W b₁ b₂) i j=W*(qCoeff P i j-qCoeff Q i j) := by
  simp only [qCoeff,physicalDifference]
  split_ifs <;> ring

theorem eval_physical_difference {n : ℕ} (P Q : Quadratic n) (W b₁ b₂ : ℤ) (x : Fin n → ℤ) :
    eval (physicalDifference P Q W b₁ b₂) x=W*(eval P x-eval Q x)+(b₁-b₂) := by
  have hL :
      (∑ i : Fin n,(physicalDifference P Q W b₁ b₂).linear i*x i)=
      W*((∑ i : Fin n,P.linear i*x i)-(∑ i : Fin n,Q.linear i*x i)) := by
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change W*(P.linear i-Q.linear i)*x i=W*(P.linear i*x i-Q.linear i*x i)
    ring
  have hQ : bilinear (physicalDifference P Q W b₁ b₂) x x =
      W*(bilinear P x x-bilinear Q x x) := by
    simp only [bilinear,physical_qCoeff,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [eval,hL,hQ]
  change W*(P.constTerm-Q.constTerm)+(b₁-b₂)+
    W*((∑ i : Fin n,P.linear i*x i)-(∑ i : Fin n,Q.linear i*x i))+
    W*(bilinear P x x-bilinear Q x x)=_
  simp only [eval]
  ring

abbrev TwoBlock (d : ℕ) := Fin (2+d)

/-- For r=1 the two independent coarse variables of (62) occupy
the first two positions; the remaining D_S fine coordinates stay. -/
def bothTranslate (d : ℕ) (a : ℤ) : TwoBlock d → ℤ :=
  fun i => if i.val<2 then a else 0

theorem bothTranslate_coarse (d : ℕ) (a : ℤ) (i : TwoBlock d) (hi : i.val<2) :
    bothTranslate d a i=a := by simp only [bothTranslate,if_pos hi]

theorem bothTranslate_fine (d : ℕ) (a : ℤ) (i : TwoBlock d) (hi : 2 ≤ i.val) :
    bothTranslate d a i=0 := by simp only [bothTranslate,if_neg (not_lt.mpr hi)]

def wrappedDifference {d : ℕ} (P Q : Quadratic (2+d))
    (W b₁ b₂ a k₁ k₂ n : ℤ) : Quadratic (2+d) :=
  translated (physicalDifference P Q W b₁ b₂) (bothTranslate d a) (W*(k₁-k₂)*n)

theorem eval_wrapped_difference {d : ℕ} (P Q : Quadratic (2+d))
    (W b₁ b₂ a k₁ k₂ n : ℤ) (x : TwoBlock d→ℤ) :
    eval (wrappedDifference P Q W b₁ b₂ a k₁ k₂ n) x =
      W*(eval P (x+bothTranslate d a)-k₁*n)+b₁ -
      (W*(eval Q (x+bothTranslate d a)-k₂*n)+b₂) := by
  rw [wrappedDifference,eval_translated,eval_physical_difference]
  ring

/-- Formal coefficients, not zero tests of polynomial functions in
small characteristic. In the affine branch there are no quadratic
terms to leak into the linear coefficient under translation. -/
abbrev Slot (n : ℕ) := (Fin n×Fin n) ⊕ Fin n

def coeff {n : ℕ} (Q : Quadratic n) : Slot n→ℤ
  | Sum.inl ij => qCoeff Q ij.1 ij.2
  | Sum.inr i => Q.linear i

def Lead {n : ℕ} (Q : Quadratic n) (m : Slot n) : Prop :=
  coeff Q m≠0 ∧ match m with
  | Sum.inl _ => True
  | Sum.inr _ => ∀ i j,qCoeff Q i j=0

theorem same_leading_coeff {n : ℕ} (Q : Quadratic n) (m : Slot n) (h : Lead Q m)
    (s : Fin n→ℤ) (wrap : ℤ) : coeff (translated Q s wrap) m=coeff Q m := by
  cases m with
  | inl ij => exact qCoeff_translated Q s wrap ij.1 ij.2
  | inr i =>
    have hz : ∀ j k,qCoeff Q j k=0 := h.2
    simp only [coeff,translated,hz,zero_mul,Finset.sum_const_zero,add_zero]

/-- Exactly the formal condition that all positive-degree
coefficients vanish modulo p. A single surviving coefficient controls
even the larger set of such primes, before testing constants. -/
def GloballyBad {n : ℕ} (Q : Quadratic n) (p : ℕ) : Prop :=
  ∀ t : Slot n,(p:ℤ)∣coeff Q t

theorem wrapped_bad_dvd_same {d : ℕ} (P Q : Quadratic (2+d))
    (W b₁ b₂ : ℤ) (m : Slot (2+d)) (hm : Lead (physicalDifference P Q W b₁ b₂) m)
    (a k₁ k₂ n : ℤ) (p : ℕ)
    (hb : GloballyBad (wrappedDifference P Q W b₁ b₂ a k₁ k₂ n) p) :
    (p:ℤ)∣coeff (physicalDifference P Q W b₁ b₂) m := by
  have hh := hb m
  rw [wrappedDifference,same_leading_coeff _ _ hm] at hh
  exact hh

/-- Even if the boundary shift and the two wrap constants are chosen
differently for each bad prime, exactly ONE marked physical signed
coefficient controls the product and the reciprocal sum. -/
theorem actual_bad_prime_budget {d : ℕ} (P Q : Quadratic (2+d))
    (W b₁ b₂ n : ℤ) (m : Slot (2+d)) (hm : Lead (physicalDifference P Q W b₁ b₂) m)
    (S : Finset ℕ) {y : ℕ} (hy : 1<y)
    (h : ∀ p∈S,p.Prime ∧ y<p ∧ ∃ a k₁ k₂ : ℤ,
      GloballyBad (wrappedDifference P Q W b₁ b₂ a k₁ k₂ n) p) :
    let c := coeff (physicalDifference P Q W b₁ b₂) m
    (∏ p∈S,p)∣c.natAbs ∧
    (∑ p∈S,1/(p:ℝ))≤Real.log (c.natAbs:ℝ)/((y:ℝ)*Real.log (y:ℝ)) := by
  let c := coeff (physicalDifference P Q W b₁ b₂) m
  have hc : c≠0 := hm.1
  have hp : ∀ p∈S,p.Prime ∧ y≤p ∧ (p:ℤ)∣c := by
    intro p hp
    obtain ⟨hprime,hy',a,k₁,k₂,hb⟩ := h p hp
    exact ⟨hprime,hy'.le,wrapped_bad_dvd_same P Q W b₁ b₂ m hm a k₁ k₂ n p hb⟩
  exact ⟨bad_product_dvd_abs S c (fun p hp' => ⟨(hp p hp').1,(hp p hp').2.2⟩),
    bad_reciprocal_le S hy hc hp⟩

end ActualTZTwoBlockCoefficients318
