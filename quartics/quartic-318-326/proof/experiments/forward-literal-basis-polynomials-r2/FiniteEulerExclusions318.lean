module
public import ActualGaussianEulerModel318
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public section
noncomputable section
namespace FiniteEulerExclusions318
open ActualGaussianEulerModel318 ActualGaussianDirichlet318
open scoped BigOperators Topology
set_option maxHeartbeats 1000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def excludedNat (κ : ℤ) (γ : J → ℤ) : Finset ℕ :=
  (FixedSieveExceptionalPrimes318.exceptionalPrimes κ γ ∪
    Finset.range (16*(Fintype.card J+2))).filter Nat.Prime

@[expose] def excluded (κ : ℤ) (γ : J → ℤ) : Finset Nat.Primes :=
  (excludedNat κ γ).attach.map {
    toFun := fun p => ⟨p.1,(Finset.mem_filter.mp p.2).2⟩
    inj' := by intro a b h; apply Subtype.ext; exact congrArg Subtype.val h }

lemma mem_excluded (κ : ℤ) (γ : J → ℤ) (p : Nat.Primes) :
    p∈excluded κ γ ↔ (p:ℕ)∈excludedNat κ γ := by
  classical
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp h
    have hev : q.1=p.1 := congrArg Subtype.val he
    exact hev ▸ q.2
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨⟨p.1,h⟩,Finset.mem_attach _ _,?_⟩
    apply Subtype.ext
    rfl

/-- Exactly the original eligibility predicate, not a conveniently enlarged
set whose missing local factors would change the constant. -/
theorem outside_iff (κ : ℤ) (γ : J → ℤ) (p : Nat.Primes) :
    p∉excluded κ γ ↔ ActualSieveEulerProduct318.Eligible κ γ (p:ℕ) := by
  rw [mem_excluded]
  simp only [excludedNat,Finset.mem_filter,Finset.mem_union,Finset.mem_range,p.2,and_true,
    ActualSieveEulerProduct318.Eligible,true_and,not_or,not_lt]

@[expose] def omittedProduct (κ : ℤ) (γ : J → ℤ) (s : ℂ) : ℂ :=
  ∏ p∈excluded κ γ, localModel (Fintype.card J) s p

lemma model_nonzero (k : ℕ) (s : ℂ) (hs : 1<s.re) (p : Nat.Primes) :
    localModel k s p≠0 := by
  have hv : modelValue k s≠0 := by
    exact mul_ne_zero (pow_ne_zero k (inv_ne_zero (riemannZeta_ne_zero_of_one_le_re hs.le)))
      (pow_ne_zero 2 (inv_ne_zero (value_nonzero s hs.le)))
  intro he
  have hz : HasProd (localModel k s) 0 := hasProd_zero_of_exists_eq_zero ⟨p,he⟩
  exact hv ((model_hasProd k s hs).unique hz)

@[expose] def realLocalOne (k : ℕ) (p : Nat.Primes) : ℝ :=
  (1-(p:ℝ)⁻¹)^k*(1-(ZMod.χ₄ (p:ZMod 4):ℝ)*(p:ℝ)⁻¹)^2

lemma real_local_positive (k : ℕ) (p : Nat.Primes) : 0<realLocalOne k p := by
  have hp : (1:ℝ)<p := by exact_mod_cast p.2.one_lt
  have hp0 : (0:ℝ)<p := by linarith
  have hx : (p:ℝ)⁻¹<1 := (inv_lt_one₀ hp0).mpr hp
  have hx0 : 0≤(p:ℝ)⁻¹ := le_of_lt (inv_pos.mpr hp0)
  have he : (ZMod.χ₄ (p:ZMod 4):ℝ)≤1 := by
    rcases ZMod.isQuadratic_χ₄ (p:ZMod 4) with h|h|h
    all_goals rw [h]; norm_num
  have heb := mul_le_mul_of_nonneg_right he hx0
  apply mul_pos (pow_pos (by linarith) k) (sq_pos_of_pos _)
  linarith

lemma model_one (k : ℕ) (p : Nat.Primes) :
    localModel k 1 p=(realLocalOne k p:ℂ) := by
  simp only [localModel,realLocalOne,Complex.cpow_neg_one,character_apply]
  push_cast
  rfl

lemma model_continuous (k : ℕ) (p : Nat.Primes) : Continuous (fun s : ℂ => localModel k s p) := by
  have hp : (p:ℂ)≠0 := by exact_mod_cast p.2.ne_zero
  have hc : Continuous (fun s : ℂ => (p:ℂ)^(-s)) :=
    continuous_neg.const_cpow (Or.inl hp)
  exact ((continuous_const.sub hc).pow k).mul
    ((continuous_const.sub (continuous_const.mul hc)).pow 2)

lemma omitted_continuous (κ : ℤ) (γ : J → ℤ) : Continuous (omittedProduct κ γ) := by
  classical
  unfold omittedProduct
  exact continuous_finsetProd _ (fun p hp => model_continuous _ p)

lemma omitted_one_nonzero (κ : ℤ) (γ : J → ℤ) : omittedProduct κ γ 1≠0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [model_one]
  exact_mod_cast (ne_of_gt (real_local_positive (Fintype.card J) p))

lemma omitted_one_positive (κ : ℤ) (γ : J → ℤ) :
    ∃ D : ℝ, 0<D ∧ omittedProduct κ γ 1=(D:ℂ) := by
  classical
  refine ⟨∏ p∈excluded κ γ, realLocalOne (Fintype.card J) p,?_,?_⟩
  · exact Finset.prod_pos (fun p hp => real_local_positive _ p)
  · simp only [omittedProduct,model_one]
    push_cast

end FiniteEulerExclusions318
