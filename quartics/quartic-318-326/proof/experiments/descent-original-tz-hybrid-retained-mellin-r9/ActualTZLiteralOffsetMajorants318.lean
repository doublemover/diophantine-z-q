module
public import ActualTZLiteralProbeSpecialization318
import all ActualTZLiteralProbeSpecialization318
import all ActualTZJointPolynomialForms318
import all ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZLiteralOffsetMajorants318
open ActualTZLiteralProbeSpecialization318 ActualTZLiteralTerminalLift318
open ActualTZJointPolynomialForms318 ActualTZTwoBlockCoefficients318
open scoped BigOperators

variable {m a b j : ℕ}

structure FineBounds (Q : Quadratic m) (A : ℤ) : Prop where
  c : |Q.constTerm|≤A
  l : ∀ i,|Q.linear i|≤A
  q : ∀ i t,|qCoeff Q i t|≤A

/-- A separates potentially larger fine coefficients from T, the
actual small pure-coarse coefficients. A single generic A for both
would NOT yield a uniform wrap cardinal on the literal thin scale. -/
structure Bounds (S : Terminal m a b) (A T : ℤ) : Prop where
  a0 : 0≤A
  t0 : 0≤T
  lin : ∀ i l,|S.slopeCoeff i l|≤A
  lconst : ∀ i,FineBounds (S.constTerm i) A
  quad : ∀ i,|S.quadratic i|≤T
  sl0 : ∀ i,|S.nonlinearSlope0 i|≤T
  nlin : ∀ i l,|S.nonlinearSlopeCoeff i l|≤A
  nconst : ∀ i,FineBounds (S.nonlinearConst i) A

private theorem bound_sum {I : Type*} [Fintype I] (f : I→ℤ) (V : ℤ)
    (H : ∀ i,|f i|≤V) : |∑ i : I,f i|≤(Fintype.card I:ℤ)*V := by
  calc
    _ ≤ ∑ i : I,|f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I,V := Finset.sum_le_sum fun i _=>H i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

private theorem fine_eval (Q : Quadratic m) (A M H U : ℤ) (hA : 0≤A)
    (hM : 0≤M) (hH : 1≤H) (hMH : M≤H)
    (hU₁ : A≤U) (hU₂ : A*M*H≤U) (B : FineBounds Q A)
    (h : Fin m→ℤ) (hh : ∀ i,|h i|≤M) :
    |eval Q h|≤(1+(m:ℤ)+(m:ℤ)^2)*U := by
  have hs : (m:ℤ)*(A*M)≤(m:ℤ)*U := by
    have a : A*M≤A*M*H := by nlinarith [mul_nonneg hA hM,
      mul_nonneg (mul_nonneg hA hM) (show 0≤H-1 by linarith)]
    exact mul_le_mul_of_nonneg_left (a.trans hU₂) (by positivity)
  have hq : (m:ℤ)*((m:ℤ)*(A*M*M))≤(m:ℤ)^2*U := by
    have a : A*M*M≤A*M*H := mul_le_mul_of_nonneg_left hMH (mul_nonneg hA hM)
    have A' := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (a.trans hU₂) (show 0≤(m:ℤ) by positivity))
      (show 0≤(m:ℤ) by positivity)
    nlinarith only [A']
  have hLin : |∑ i : Fin m,Q.linear i*h i|≤(m:ℤ)*(A*M) := by
    simpa only [Fintype.card_fin] using bound_sum (fun i : Fin m=>Q.linear i*h i) (A*M)
      (fun i=>by rw [abs_mul]; exact mul_le_mul (B.l i) (hh i) (abs_nonneg _) hA)
  have hQuad : |bilinear Q h h| ≤(m:ℤ)*((m:ℤ)*(A*M*M)) := by
    unfold bilinear
    have inner (i : Fin m) : |∑ t : Fin m,qCoeff Q i t*h i*h t|≤(m:ℤ)*(A*M*M) := by
      simpa only [Fintype.card_fin] using
        bound_sum (fun t : Fin m=>qCoeff Q i t*h i*h t) (A*M*M)
        (fun t=>by
          simp only [abs_mul]
          exact mul_le_mul (mul_le_mul (B.q i t) (hh i) (abs_nonneg _) hA)
            (hh t) (abs_nonneg _) (mul_nonneg hA hM))
    simpa only [Fintype.card_fin] using bound_sum
      (fun i : Fin m=>∑ t : Fin m,qCoeff Q i t*h i*h t) ((m:ℤ)*(A*M*M)) inner
  unfold eval
  have H₁ := abs_add_le (Q.constTerm+∑ i : Fin m,Q.linear i*h i) (bilinear Q h h)
  have H₂ := abs_add_le Q.constTerm (∑ i : Fin m,Q.linear i*h i)
  nlinarith only [H₁,H₂,hLin,hQuad,B.c,hU₁,hs,hq]

def linConst (m a : ℕ) : ℕ := m+(1+m+m^2)+2*a*m
def nonlinConst (m a : ℕ) : ℕ := (1+a)^2+(1+a)*(1+m)+(1+m+m^2)+a*m
def cap (m a : ℕ) : ℕ := a*m+linConst m a+nonlinConst m a

/-- All actual offset formulas, proven with the peeled coefficient
scales. U can be C_H n for the true carrier, or an effective
poly(W) bound at the tiny ±2 probe samples. -/
theorem offset_bound (S : Terminal m a b) (u : Site a b j)
    (A T M H U : ℤ) (B : Bounds S A T) (hM : 0≤M) (hH : 1≤H) (hMH : M≤H)
    (hA : A≤U) (hFine : A*M*H≤U) (hCoarse : T*H^2≤U)
    (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ)
    (hh : ∀ i,|h i|≤M) (hk : ∀ e i,|k e i|≤M) (hc : ∀ t,|c t|≤H) :
    |eOffset S u h k c|≤(cap m a:ℤ)*U := by
  have hA0 : 0≤A := B.a0
  have hT0 : 0≤T := B.t0
  have hU : 0≤U := hA0.trans hA
  have hAm : A*M*M≤U := (mul_le_mul_of_nonneg_left hMH (mul_nonneg B.a0 hM)).trans hFine
  have hs (i : Fin a) : |slope S i h|≤(m:ℤ)*(A*M) := by
    unfold slope
    simpa only [Fintype.card_fin] using bound_sum (fun l : Fin m=>S.slopeCoeff i l*h l) (A*M)
      (fun l=>by rw [abs_mul]; exact mul_le_mul (B.lin i l) (hh l) (abs_nonneg _) B.a0)
  have hn (i : Fin b) : |nonlinearSlope S i h|≤T+(m:ℤ)*(A*M) := by
    unfold nonlinearSlope
    refine (abs_add_le _ _).trans (add_le_add (B.sl0 i) ?_)
    simpa only [Fintype.card_fin] using bound_sum (fun l : Fin m=>S.nonlinearSlopeCoeff i l*h l)
      (A*M) (fun l=>by rw [abs_mul]; exact mul_le_mul (B.nlin i l) (hh l) (abs_nonneg _) B.a0)
  have mk (ω : Bits a) : |∑ i : Fin a,slope S i h*k (ω i) i|≤(a:ℤ)*(m:ℤ)*U := by
    have t := bound_sum (fun i : Fin a=>slope S i h*k (ω i) i) ((m:ℤ)*U) (fun i=>by
      rw [abs_mul]
      have H₀ := mul_le_mul (hs i) (hk (ω i) i) (abs_nonneg _) (by positivity)
      exact H₀.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hAm (by positivity)))
    simpa only [Fintype.card_fin,mul_assoc] using t
  cases u with
  | marked ω =>
      unfold eOffset
      rw [abs_neg]
      refine (mk ω).trans ?_
      unfold cap
      push_cast
      have HH : (0:ℤ)≤(linConst m a:ℤ)+(nonlinConst m a:ℤ) := by positivity
      nlinarith only [mul_nonneg HH hU]
  | linear t i ω =>
      have hL : |slope S i h*c t|≤(m:ℤ)*U := by
        rw [abs_mul]
        have H₀ := mul_le_mul (hs i) (hc t) (abs_nonneg _) (by positivity)
        exact H₀.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hFine (by positivity))
      have hF : |eval (S.constTerm i) h|≤(1+(m:ℤ)+(m:ℤ)^2)*U :=
        fine_eval _ A M H U B.a0 hM hH hMH hA hFine (B.lconst i) h hh
      have hFcap : Fintype.card {v : Fin a // v≠i}≤a := by
        simpa only [Fintype.card_fin] using
          (Fintype.card_le_of_injective (fun v : {v : Fin a // v≠i}=>v.val) Subtype.val_injective)
      have hF0 : |∑ v : {u : Fin a // u≠i},
          (slope S i h-slope S v.val h)*k (ω v) v.val|≤(a:ℤ)*2*(m:ℤ)*U := by
        have H₀ := bound_sum (fun v : {u : Fin a // u≠i}=>
          (slope S i h-slope S v.val h)*k (ω v) v.val) (2*(m:ℤ)*U) (fun v=>by
            have H₁ := (abs_sub_le _ _).trans (add_le_add (hs i) (hs v.val))
            rw [abs_mul]
            have H₂ := mul_le_mul H₁ (hk (ω v) v.val) (abs_nonneg _) (by positivity)
            have H₃ := mul_le_mul_of_nonneg_left hAm (show 0≤2*(m:ℤ) by positivity)
            nlinarith only [H₂,H₃])
        have H₁ := mul_le_mul_of_nonneg_right (show
          (Fintype.card {v : Fin a // v≠i}:ℤ)≤a by exact_mod_cast hFcap)
          (show 0≤2*(m:ℤ)*U by positivity)
        nlinarith only [H₀,H₁]
      unfold eOffset
      have H₁ := abs_add_le (slope S i h*c t+eval (S.constTerm i) h)
        (∑ v : {u : Fin a // u≠i},(slope S i h-slope S v.val h)*k (ω v) v.val)
      have H₂ := abs_add_le (slope S i h*c t) (eval (S.constTerm i) h)
      have hcap : (linConst m a:ℤ)≤cap m a := by
        unfold cap
        push_cast
        linarith [show (0:ℤ)≤(a:ℤ)*(m:ℤ) by positivity, Nat.cast_nonneg (nonlinConst m a)]
      have hcap' := mul_le_mul_of_nonneg_right hcap hU
      unfold linConst at hcap'
      push_cast at hcap'
      nlinarith only [H₁,H₂,hL,hF,hF0,hcap']
  | nonlinear t i ω =>
      let z := c t+∑ l : Fin a,k (ω l) l
      have hZ₀ : |z|≤H+(a:ℤ)*M := by
        exact (abs_add_le _ _).trans (add_le_add (hc t)
          (by simpa only [Fintype.card_fin] using bound_sum (fun l : Fin a=>k (ω l) l) M
            (fun l=>hk (ω l) l)))
      have hz : |z|≤(1+(a:ℤ))*H := by
        have h0 := mul_le_mul_of_nonneg_left hMH (show 0≤(a:ℤ) by positivity)
        nlinarith only [hZ₀,h0]
      have Q : |S.quadratic i*z^2|≤(1+(a:ℤ))^2*U := by
        rw [abs_mul,abs_pow]
        have H₁ := mul_le_mul (B.quad i) (pow_le_pow_left₀ (abs_nonneg _) hz 2)
          (sq_nonneg _) B.t0
        have H₂ := mul_le_mul_of_nonneg_left hCoarse
          (sq_nonneg (1+(a:ℤ)))
        nlinarith only [H₁,H₂]
      have C : |nonlinearSlope S i h*z|≤(1+(a:ℤ))*(1+(m:ℤ))*U := by
        rw [abs_mul]
        have H₁ := mul_le_mul (hn i) hz (abs_nonneg _) (by positivity)
        have HT : T*H≤U := by
          have hh' : T*H≤T*H^2 := by
            nlinarith [mul_nonneg (mul_nonneg B.t0 (show 0≤H by linarith))
                (show 0≤H-1 by linarith)]
          exact hh'.trans hCoarse
        have H₂ := mul_le_mul_of_nonneg_left HT (show 0≤1+(a:ℤ) by positivity)
        have H₃ := mul_le_mul_of_nonneg_left hFine (show 0≤(1+(a:ℤ))*(m:ℤ) by positivity)
        nlinarith only [H₁,H₂,H₃]
      have f : |eval (S.nonlinearConst i) h|≤(1+(m:ℤ)+(m:ℤ)^2)*U :=
        fine_eval _ A M H U B.a0 hM hH hMH hA hFine (B.nconst i) h hh
      change |S.quadratic i*z^2+nonlinearSlope S i h*z+eval (S.nonlinearConst i) h-
          ∑ l : Fin a,slope S l h*k (ω l) l|≤_
      have H₁ := abs_sub_le (S.quadratic i*z^2+nonlinearSlope S i h*z+
        eval (S.nonlinearConst i) h) (∑ l : Fin a,slope S l h*k (ω l) l)
      have H₂ := abs_add_le (S.quadratic i*z^2+nonlinearSlope S i h*z)
        (eval (S.nonlinearConst i) h)
      have H₃ := abs_add_le (S.quadratic i*z^2) (nonlinearSlope S i h*z)
      have hcap : (nonlinConst m a:ℤ)≤cap m a := by
        unfold cap
        push_cast
        linarith [show (0:ℤ)≤(a:ℤ)*(m:ℤ) by positivity, Nat.cast_nonneg (linConst m a)]
      have hcap' := mul_le_mul_of_nonneg_right hcap hU
      unfold nonlinConst at hcap'
      push_cast at hcap'
      nlinarith only [H₁,H₂,H₃,Q,C,f,mk ω,hcap']

end ActualTZLiteralOffsetMajorants318
