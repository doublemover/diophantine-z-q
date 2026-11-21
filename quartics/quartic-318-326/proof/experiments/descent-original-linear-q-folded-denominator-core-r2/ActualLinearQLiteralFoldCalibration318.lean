module
public import ActualLinearQOrderOneCalibration318
public import Mathlib.NumberTheory.Padics.PadicNumbers
public section
noncomputable section
namespace ActualLinearQLiteralFoldCalibration318

open ActualLinearQArithmeticCalibration318

/-- The tags are exactly q1/q4/q13, and the 16 coefficient pairs
are listed in original source order, including unsquared conjugate
ordinate differences. The input has the historical ℕ→ℚ form. -/
@[expose] def coefficients (w : ℕ → ℚ) : List (Fin 3 × (ℚ × ℚ)) :=
  [(1,(w 126,0)),
   (0,(w 125,0)),
   (0,(w 58,2*w 59)),
   (0,(w 60,2*w 61)),
   (0,(2*w 62,2*w 63)),
   (0,(w 64,2*w 65)),
   (0,(w 19-1,-w 20)),
   (0,(w 23-1,-w 24)),
   (0,(w 27-1,-w 28)),
   (0,(w 31-1,-w 32)),
   (1,(w 127,2*w 128)),
   (2,(w 129,2*w 130)),
   (2,(w 131,2*w 132)),
   (2,(w 133,2*w 134)),
   (1,(110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729,
      -7446*w 103-29784*w 136)),
   (2,(-2*w 123+w 137+1,-4*w 124+4*w 138))]

@[expose] def weights (c u A q : ℚ) : Fin 3 → ℚ :=
  ![weight c u A q,
    (weight c u A q)^7*(delta c u A q)^18,
    (weight c u A q)^25*(delta c u A q)^72]

/-- Explicit Q(√2) pair step from the original 16-leaf fold. -/
@[expose] def step (x e : ℚ × ℚ) : ℚ × ℚ :=
  (x.1^2+2*x.2^2+e.1,2*x.1*x.2+e.2)

@[expose] def fold (w : ℕ → ℚ) (c u A q : ℚ) : ℚ × ℚ :=
  ((coefficients w).map (fun m =>
    (weights c u A q m.1*m.2.1,weights c u A q m.1*m.2.2))).foldl step (1,0)

@[expose] def trace (x : ℚ × ℚ) : ℚ := (x.1^2-2*x.2^2)/(2*x.1)

/-- The valuation is extended at zero. This is needed for zero
unweighted coefficients; padicValRat by itself is zero at zero. -/
noncomputable def val (p : ℕ) [Fact p.Prime] : AddValuation ℚ (WithTop ℤ) :=
  Padic.addValuation.comap (algebraMap ℚ ℚ_[p])

theorem val_rat (p : ℕ) [Fact p.Prime] (z : ℚ) (hz : z ≠ 0) :
    val p z = (padicValRat p z:WithTop ℤ) := by
  change Padic.addValuation (z:ℚ_[p]) = _
  rw [Padic.addValuation.apply (by exact_mod_cast hz),Padic.valuation_ratCast]

private theorem near_one_value (v : AddValuation ℚ (WithTop ℤ)) (x : ℚ)
    (h : 0 < v (x-1)) : v x = 0 := by
  simpa using v.map_eq_of_lt_sub (x:=1) (y:=x) (by simpa using h)

private theorem add_positive (v : AddValuation ℚ (WithTop ℤ)) (x y : ℚ)
    (hx : 0 < v x) (hy : 0 < v y) : 0 < v (x+y) :=
  lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)

private theorem mul_pos_of_right (v : AddValuation ℚ (WithTop ℤ)) (x y : ℚ)
    (hx : 0 < v x) (hy : 0 ≤ v y) : 0 < v (x*y) := by
  rw [v.map_mul]
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy)

private theorem halo_square (v : AddValuation ℚ (WithTop ℤ)) (x : ℚ)
    (hx : 0 < v (x-1)) : 0 < v (x^2-1) := by
  have h := near_one_value v x hx
  have ha : 0 ≤ v (x+1) := by simpa [h] using v.map_add x 1
  rw [show x^2-1=(x-1)*(x+1) by ring]
  exact mul_pos_of_right v _ _ hx ha

/-- The actual pair fold specializes to (1,0), not two unrelated
one-coordinate recurrences. A zero error has infinite depth. -/
theorem folded_near (v : AddValuation ℚ (WithTop ℤ)) (h2 : 0 ≤ v (2:ℚ))
    (xs : List (ℚ × ℚ)) (x : ℚ × ℚ)
    (hx : 0 < v (x.1-1) ∧ 0 < v x.2)
    (hxs : ∀ e ∈ xs, 0 < v e.1 ∧ 0 < v e.2) :
    0 < v ((xs.foldl step x).1-1) ∧ 0 < v (xs.foldl step x).2 := by
  induction xs generalizing x with
  | nil => exact hx
  | cons e xs ih =>
    have hx0 := near_one_value v x.1 hx.1
    have hx2 : 0 < v (x.2^2) := by
      rw [pow_two]
      exact mul_pos_of_right v _ _ hx.2 hx.2.le
    have hB : 0 < v (2*x.2^2) := by
      rw [mul_comm (2:ℚ)]
      exact mul_pos_of_right v _ _ hx2 h2
    have hC : 0 ≤ v (2*x.1) := by rw [v.map_mul,hx0,add_zero]; exact h2
    obtain ⟨heR,heI⟩ := hxs e (by simp)
    have hnext : 0 < v ((step x e).1-1) ∧ 0 < v (step x e).2 := by
      constructor
      · change 0 < v (x.1^2+2*x.2^2+e.1-1)
        rw [show x.1^2+2*x.2^2+e.1-1=(x.1^2-1)+2*x.2^2+e.1 by ring]
        exact add_positive v _ _ (add_positive v _ _ (halo_square v x.1 hx.1) hB) heR
      · change 0 < v (2*x.1*x.2+e.2)
        rw [mul_comm (2*x.1) x.2]
        exact add_positive v _ _ (mul_pos_of_right v _ _ hx.2 hC) heI
    exact ih _ hnext (fun a ha => hxs a (List.mem_cons_of_mem _ ha))

private theorem trace_of_near (p : ℕ) [Fact p.Prime] (x : ℚ × ℚ)
    (h2 : val p (2:ℚ) = 0) (hx : 0 < val p (x.1-1) ∧ 0 < val p x.2) :
    trace x ≠ 0 ∧ padicValRat p (trace x) = 0 := by
  let v := val p
  have ha := near_one_value v x.1 hx.1
  have ha0 : x.1 ≠ 0 := (v.ne_top_iff).mp (by rw [ha]; simp)
  have hb : 0 < v (2*x.2^2) := by
    rw [mul_comm (2:ℚ),pow_two]
    exact mul_pos_of_right v _ _ (mul_pos_of_right v _ _ hx.2 hx.2.le) h2.ge
  have hn := add_positive v (x.1^2-1) (-(2*x.2^2))
    (halo_square v x.1 hx.1) (by simpa only [v.map_neg] using hb)
  have hn' : 0 < v ((x.1^2-2*x.2^2)-1) := by
    rw [show (x.1^2-2*x.2^2)-1=(x.1^2-1)+(-(2*x.2^2)) by ring]
    exact hn
  have hN := near_one_value v _ hn'
  have hN0 : x.1^2-2*x.2^2 ≠ 0 := (v.ne_top_iff).mp (by rw [hN]; simp)
  have hτ : trace x ≠ 0 := div_ne_zero hN0 (mul_ne_zero (by decide) ha0)
  have hv : v (trace x) = 0 := by
    rw [trace,v.map_div,v.map_mul,hN,h2,ha,add_zero]
    change (((0:ℤ):WithTop ℤ) - ((0:ℤ):WithTop ℤ)) = ((0:ℤ):WithTop ℤ)
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub (0:ℤ) (0:ℤ),sub_self]
  rw [val_rat p _ hτ] at hv
  exact ⟨hτ,by exact_mod_cast hv⟩

/-- The bounded local producer after the arithmetic-only smoke. This
derives, rather than assumes, the unit trace at the literal sixteen
ordered coefficient pairs. The coefficient bounds supplied by the
same-h original chart/ratio producer are the remaining local input. -/
theorem order_one_gate (p : ℕ) [Fact p.Prime] (hp : 2399 < p)
    (w : ℕ → ℚ) (c u A : ℚ)
    (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0)
    (hc0 : padicValRat p c = 0) (hu0 : padicValRat p u = 0) (hA0 : padicValRat p A = 0)
    (hCoeff : ∀ e ∈ coefficients w, 0 ≤ val p e.2.1 ∧ 0 ≤ val p e.2.2) :
    trace (fold w c u A p) ≠ 0 ∧
      padicValRat p (trace (fold w c u A p)) = 0 ∧
      padicValRat p (pole (trace (fold w c u A p)) c u A p) = 1 := by
  let v := val p
  obtain ⟨hF,hFV,hΔ,hΔV⟩ := ActualLinearQOrderOneCalibration318.contact_delta p hp c u A
    hc hu hA hc0 hu0 hA0
  have hW : weight c u A p ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF)
  have hwVal : padicValRat p (weight c u A p) = 3 := by
    rw [weight,padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF),
      padicValRat.div (pow_ne_zero _ hΔ) hF,padicValRat.pow,padicValRat.pow,hc0,hΔV,hFV] <;> norm_num
  have wh (i : Fin 3) : weights c u A p i ≠ 0 ∧ padicValRat p (weights c u A p i) = 3 := by
    fin_cases i
    · exact ⟨hW,hwVal⟩
    · refine ⟨mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),?_⟩
      change padicValRat p ((weight c u A p)^7*(delta c u A p)^18) = 3
      rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
        padicValRat.pow,padicValRat.pow,hwVal,hΔV] <;> norm_num
    · refine ⟨mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),?_⟩
      change padicValRat p ((weight c u A p)^25*(delta c u A p)^72) = 3
      rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
        padicValRat.pow,padicValRat.pow,hwVal,hΔV] <;> norm_num
  have hv2 : v (2:ℚ) = 0 := by
    have hn : ¬ p ∣ 2 := fun h => (by omega : ¬ p ≤ 2) (Nat.le_of_dvd (by decide) h)
    rw [val_rat p _ (by decide),show (2:ℚ)=(2:ℕ) by norm_num,
      padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hn] <;> rfl
  have hFold : 0 < v ((fold w c u A p).1-1) ∧ 0 < v (fold w c u A p).2 := by
    unfold fold
    apply folded_near v hv2.ge _ (1,0) (by simp)
    intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    have hweight : 0 < v (weights c u A p a.1) := by
      rw [val_rat p _ (wh a.1).1,(wh a.1).2] <;> norm_num
    exact ⟨mul_pos_of_right v _ _ hweight (hCoeff a ha).1,
      mul_pos_of_right v _ _ hweight (hCoeff a ha).2⟩
  obtain ⟨hne,hv⟩ := trace_of_near p _ hv2 hFold
  exact ⟨hne,hv,(ActualLinearQOrderOneCalibration318.order_only_q p hp _
    c u A hne hc hu hA hv hc0 hu0 hA0).2.2.2⟩

end ActualLinearQLiteralFoldCalibration318
