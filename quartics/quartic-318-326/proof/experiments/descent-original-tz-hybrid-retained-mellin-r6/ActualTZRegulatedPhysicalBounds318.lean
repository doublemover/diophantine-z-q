module
public import ActualTZRegulatedRelative318
public import ActualTZRegulatedPhysicalPrime318
public section
noncomputable section
namespace ActualTZRegulatedPhysicalBounds318
open scoped BigOperators
open ActualTZRegulatedRelative318 ActualTZRegulatedZetaAlgebra318
open ActualTZRegulatedPhysicalPrime318 ActualTZRegulatedLocalFactor318
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def emptyBits : Bits I := fun _ => false

private theorem empty_iff (d e : Bits I) :
    (∀ i,¬selected d e i) ↔ d=emptyBits ∧ e=emptyBits := by
  constructor
  · intro h
    constructor <;> funext i
    · cases H : d i
      · exact H
      · exact (h i (Or.inl H)).elim
    · cases H : e i
      · exact H
      · exact (h i (Or.inr H)).elim
  · rintro ⟨rfl,rfl⟩ i
    simp [selected,emptyBits]

private theorem amp_empty (z w : I→ℂ) :
    amplitude z w emptyBits emptyBits=1 := by
  simp [amplitude,pick,emptyBits]

@[expose] def factor (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ) (z w : I→ℂ) : ℂ :=
  ∑ d : Bits I,∑ e : Bits I,amplitude z w d e*physicalMass W p a b d e

def residual (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (z w : I→ℂ) (d e : Bits I) : ℂ :=
  if ∀ i,¬selected d e i then 0 else amplitude z w d e*physicalMass W p a b d e

private theorem empty_mass (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) :
    (physicalMass W p a b emptyBits emptyBits : ℂ)=1 := by
  have he : ∀ i : I,¬selected emptyBits emptyBits i := (empty_iff _ _).2 ⟨rfl,rfl⟩
  by_cases hc : W.Coprime p
  · rw [physicalMass_incident W p a b _ _ hc,if_pos he]
  · rw [physicalMass_bad W p a b _ _ hU hc,if_pos he]

/-- Extract exactly one all-off term even on a repeated-root tuple. -/
theorem factor_eq_one_add_residual (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (z w : I→ℂ) :
    factor W p a b z w=1+∑ d : Bits I,∑ e : Bits I,residual W p a b z w d e := by
  classical
  have h (d e : Bits I) :
      amplitude z w d e*physicalMass W p a b d e =
        (if d=emptyBits ∧ e=emptyBits then 1 else 0)+residual W p a b z w d e := by
    by_cases he : ∀ i,¬selected d e i
    · obtain ⟨rfl,rfl⟩ := (empty_iff d e).1 he
      simp [residual,he,amp_empty,empty_mass W p a b hU]
    · have hd : ¬(d=emptyBits ∧ e=emptyBits) := fun H => he ((empty_iff d e).2 H)
      simp [residual,he,hd]
  unfold factor
  simp_rw [h,Finset.sum_add_distrib]
  congr 1
  have hinner (d : Bits I) : (∑ e : Bits I,if d=emptyBits ∧ e=emptyBits then (1:ℂ) else 0) =
      if d=emptyBits then 1 else 0 := by
    by_cases hd : d=emptyBits <;> simp [hd]
  simp_rw [hinner]
  simp

private theorem pick_true (z : ℂ) : pick z true = -z := by simp [pick]

private theorem pick_le (z : ℂ) (t : ℝ) (hz : ‖z‖≤t) (ht : t≤1) (d : Bool) :
    ‖pick z d‖ ≤ 1 := by
  cases d
  · simp [pick]
  · simpa only [pick_true,norm_neg] using hz.trans ht

private theorem norm_prod_eq (s : Finset I) (f : I→ℂ) :
    ‖∏ i∈s,f i‖ = ∏ i∈s,‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,norm_mul,ih]

private theorem amp_small (z w : I→ℂ) (t : ℝ) (ht : t≤1)
    (hz : ∀ i,‖z i‖≤t) (hw : ∀ i,‖w i‖≤t)
    (d e : Bits I) (i : I) (hi : selected d e i) :
    ‖amplitude z w d e‖ ≤ t := by
  classical
  let f : I→ℝ := fun j => ‖pick (z j) (d j)*pick (w j) (e j)‖
  have ha (j : I) : f j ≤ 1 := by
    dsimp only [f]
    rw [norm_mul]
    exact (mul_le_mul (pick_le _ t (hz j) ht _) (pick_le _ t (hw j) ht _)
      (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hb : f i ≤ t := by
    dsimp only [f]
    rw [norm_mul]
    rcases hi with hd|he
    · rw [hd]
      simp only [pick_true,norm_neg]
      calc
        _ ≤ ‖z i‖*1 := mul_le_mul_of_nonneg_left (pick_le _ t (hw i) ht _) (norm_nonneg _)
        _ ≤ _ := by simpa only [mul_one] using hz i
    · rw [he]
      have H : ‖pick (z i) (d i)‖*‖w i‖ ≤ 1*‖w i‖ :=
        mul_le_mul_of_nonneg_right (pick_le _ t (hz i) ht _) (norm_nonneg _)
      simpa only [pick_true,norm_neg,one_mul] using H.trans (by simpa only [one_mul] using hw i)
  rw [amplitude,norm_prod_eq]
  change (∏ j : I,f j) ≤ t
  calc
    _ ≤ ∏ j : I,if j=i then f i else 1 := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j _
      by_cases H : j=i
      · simp [H]
      · simpa only [if_neg H] using ha j
    _ = f i := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ H
        simp [H]
      · simp
    _ ≤ _ := hb

private theorem inverse_norm (p : ℕ) : ‖((p:ℂ)⁻¹)‖=1/(p:ℝ) := by
  simp only [norm_inv,Complex.norm_natCast,one_div]

/-- Absolute budget for every nonempty divisor pair under a positive
regulator envelope t (the actual specialization is t=p^(-σ)).
The bound is valid even if several original roots coincide. -/
theorem residual_norm (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (z w : I→ℂ) (t : ℝ) (ht₀ : 0≤t) (ht : t≤1)
    (hz : ∀ i,‖z i‖≤t) (hw : ∀ i,‖w i‖≤t) (d e : Bits I) :
    ‖residual W p a b z w d e‖ ≤ t/(p:ℝ) := by
  by_cases h : ∀ i,¬selected d e i
  · simp only [residual,if_pos h,norm_zero]
    positivity
  · obtain ⟨i,hi⟩ : ∃ i,selected d e i := by simpa only [not_forall,not_not] using h
    rw [residual,if_neg h,norm_mul]
    by_cases hc : W.Coprime p
    · have hM : ‖(physicalMass W p a b d e : ℂ)‖ ≤ 1/(p:ℝ) := by
        rw [physicalMass_incident W p a b d e hc,if_neg h]
        split_ifs with H
        · simpa only [one_div] using le_of_eq (inverse_norm p)
        · rw [norm_zero]
          positivity
      simpa only [div_eq_mul_inv,one_mul] using
        mul_le_mul (amp_small z w t ht hz hw d e i hi) hM (norm_nonneg _) ht₀
    · rw [physicalMass_bad W p a b d e hU hc,if_neg h,norm_zero,mul_zero]
      positivity

/-- Absolute finite weight bound, before any condition on collisions
and before any passage to infinite products. -/
theorem residual_sum_norm (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (z w : I→ℂ) (t : ℝ) (ht₀ : 0≤t) (ht : t≤1)
    (hz : ∀ i,‖z i‖≤t) (hw : ∀ i,‖w i‖≤t) :
    (∑ d : Bits I,∑ e : Bits I,‖residual W p a b z w d e‖) ≤
      ((2:ℝ)^Fintype.card I)^2*(t/(p:ℝ)) := by
  calc
    _ ≤ ∑ _d : Bits I,∑ _e : Bits I,t/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro e _
      exact residual_norm W p a b hU z w t ht₀ ht hz hw d e
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Bits,Fintype.card_fun,
        Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,pow_two]
      ring

theorem factor_norm_sub (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (z w : I→ℂ) (t : ℝ) (ht₀ : 0≤t) (ht : t≤1)
    (hz : ∀ i,‖z i‖≤t) (hw : ∀ i,‖w i‖≤t) :
    ‖factor W p a b z w-1‖ ≤ ((2:ℝ)^Fintype.card I)^2*(t/(p:ℝ)) := by
  rw [factor_eq_one_add_residual W p a b hU z w,add_comm 1 _,add_sub_cancel_right]
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)).trans
    (residual_sum_norm W p a b hU z w t ht₀ ht hz hw)

theorem factor_wheel (W p : ℕ) [NeZero p] (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (z w : I→ℂ) (hc : ¬W.Coprime p) :
    factor W p a b z w=1 := by
  rw [factor_eq_one_add_residual W p a b hU z w]
  have he (d e : Bits I) : residual W p a b z w d e=0 := by
    by_cases H : ∀ i,¬selected d e i
    · simp only [residual,if_pos H]
    · rw [residual,if_neg H,physicalMass_bad W p a b d e hU hc,if_neg H,mul_zero]
  simp only [he,Finset.sum_const_zero,add_zero]

@[expose] def regulator (p : ℕ) (s : I→ℂ) : I→ℂ := fun i => (p : ℂ)^(-s i)

@[expose] def baseline (p : ℕ) (z w : I→ℂ) : ℂ :=
  ∏ i : I,oneSite ((p : ℂ)⁻¹) (z i) (w i)

private theorem regulator_bound (p : ℕ) (hp : p.Prime) (σ : ℝ) (s : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (i : I) : ‖regulator p s i‖ ≤ (p:ℝ)^(-σ) := by
  rw [regulator,Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (neg_le_neg (hs i))

private theorem inverse_le_half (p : ℕ) (hp : p.Prime) : ‖((p:ℂ)⁻¹)‖≤1/2 := by
  rw [inverse_norm]
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
  exact_mod_cast hp.two_le

/-- Absolute local nonempty weight at a genuinely fixed positive
real part. Holds uniformly in the intercepts, including collisions,
and in the wheel. This estimate is not uniform as σ tends to zero. -/
theorem fixed_regulator_budget (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    (∑ d : Bits I,∑ e : Bits I,‖residual W p a b (regulator p s) (regulator p u) d e‖) ≤
      ((2:ℝ)^Fintype.card I)^2*(p:ℝ)^(-1-σ) := by
  let t : ℝ := (p:ℝ)^(-σ)
  have h₀ : 0≤t := by dsimp only [t]; positivity
  have h₁ : t≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hp.one_lt.le) (by linarith)
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have he : t/(p:ℝ)=(p:ℝ)^(-1-σ) := by
    dsimp only [t]
    rw [show -1-σ=(-σ)-(1:ℝ) by ring,Real.rpow_sub hp',Real.rpow_one]
  rw [←he]
  exact residual_sum_norm W p a b hU _ _ t h₀ h₁
    (regulator_bound p hp σ s hs) (regulator_bound p hp σ u hu)

theorem relative_regulated_distinct (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ) (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re)
    (hc : W.Coprime p) (hDistinct : Function.Injective (primeRoot W p a b)) :
    ‖factor W p a b (regulator p s) (regulator p u) /
      baseline p (regulator p s) (regulator p u)-1‖ ≤
      (6:ℝ)^Fintype.card I*(errorConst (Fintype.card I)*(1/(p:ℝ))^2) := by
  let z := regulator p s
  let w := regulator p u
  have ht : (p:ℝ)^(-σ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hp.one_lt.le) (by linarith)
  have hz (i : I) : ‖z i‖≤1 := (regulator_bound p hp σ s hs i).trans ht
  have hw (i : I) : ‖w i‖≤1 := (regulator_bound p hp σ u hu i).trans ht
  have hE : factor W p a b z w=1+((p:ℂ)⁻¹)*(∑ i : I,correction (z i) (w i)) := by
    unfold factor
    rw [local_good W p a b z w hc,distinct_correction _ hDistinct]
    simp only [correction,div_eq_mul_inv]
    congr 1
    exact mul_comm _ _
  change ‖factor W p a b z w/baseline p z w-1‖≤_
  rw [hE]
  simpa only [baseline,Finset.card_univ,inverse_norm] using
    noncollision_relative Finset.univ ((p:ℂ)⁻¹) z w (inverse_le_half p hp) hz hw

/-- For an off-wheel collision (or without assuming distinctness),
a true linear relative estimate with explicit constant. -/
theorem relative_regulated_linear (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ)
    (s u : I→ℂ) (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    ‖factor W p a b (regulator p s) (regulator p u) /
      baseline p (regulator p s) (regulator p u)-1‖ ≤
    (6:ℝ)^Fintype.card I*
      ((((2:ℝ)^Fintype.card I)^2*(p:ℝ)^(-σ)+3*(Fintype.card I:ℝ)+errorConst (Fintype.card I))*
        (1/(p:ℝ))) := by
  let z := regulator p s
  let w := regulator p u
  let t : ℝ := (p:ℝ)^(-σ)
  have ht₀ : 0≤t := by dsimp only [t]; positivity
  have ht : t≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hp.one_lt.le) (by linarith)
  have hz (i : I) : ‖z i‖≤1 := (regulator_bound p hp σ s hs i).trans ht
  have hw (i : I) : ‖w i‖≤1 := (regulator_bound p hp σ u hu i).trans ht
  have H : ‖factor W p a b z w-1‖ ≤ (((2:ℝ)^Fintype.card I)^2*t)*‖((p:ℂ)⁻¹)‖ := by
    rw [inverse_norm]
    have H₀ := factor_norm_sub W p a b hU z w t ht₀ ht
      (regulator_bound p hp σ s hs) (regulator_bound p hp σ u hu)
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using H₀
  change ‖factor W p a b z w/baseline p z w-1‖≤_
  simpa only [baseline,Finset.card_univ,inverse_norm,t] using
    relative_of_linear Finset.univ ((p:ℂ)⁻¹) (factor W p a b z w) z w
      (((2:ℝ)^Fintype.card I)^2*t) (inverse_le_half p hp) hz hw H

/-- Literal trichotomy key: retain divisibility of an actual signed
intercept difference rather than a different bound on a formal marker. -/
theorem collision_witness (W p : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hc : W.Coprime p) :
    (¬Function.Injective (primeRoot W p a b)) ↔
      ∃ i j,i≠j ∧ (p:ℤ)∣ActualTZMultiLinearCRT318.physicalConst W a b i -
        ActualTZMultiLinearCRT318.physicalConst W a b j := by
  classical
  constructor
  · intro H
    by_contra Hn
    apply H
    intro i j he
    by_contra hn
    exact Hn ⟨i,j,hn,(root_collision W p a b i j hc).mp he⟩
  · rintro ⟨i,j,hn,hd⟩ H
    exact hn (H ((root_collision W p a b i j hc).mpr hd))

theorem wheel_regulated (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (hd : p∣W) (s u : I→ℂ) :
    factor W p a b (regulator p s) (regulator p u)=1 :=
  factor_wheel W p a b hU _ _
    (fun h => (hp.dvd_iff_not_coprime.mp hd) h.symm)

/-- At a genuinely distinct integer specialization every prime
outside the actual source finite bad set and W gets the quadratic
estimate. No bound on the size of that set has been added. -/
theorem relative_regulated_off_bad_set
    (W p : ℕ) [NeZero p] (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ) (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re)
    (hW : ¬p∣W) (hDistinct : Function.Injective
      (ActualTZMultiLinearCRT318.physicalConst W a b))
    (hBad : p∉collisionPrimes W a b) :
    ‖factor W p a b (regulator p s) (regulator p u) /
      baseline p (regulator p s) (regulator p u)-1‖ ≤
      (6:ℝ)^Fintype.card I*(errorConst (Fintype.card I)*(1/(p:ℝ))^2) := by
  have hc : W.Coprime p := (hp.coprime_iff_not_dvd.mpr hW).symm
  exact relative_regulated_distinct W p hp a b σ hσ s u hs hu hc
    (root_injective_off W p a b hp hc hDistinct hBad)

def primeAbsoluteBudget (W : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ)
    (p : {p : ℕ // p.Prime}) : ℝ := by
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  exact ∑ d : Bits I,∑ e : Bits I,
    ‖residual W p.val a b (regulator p.val s) (regulator p.val u) d e‖

/-- Absolute sum of the nonempty local choices at FIXED σ>0. The
termwise dominance is independent of W and of the signed tuple.
This does not assert a uniform Mellin-frequency estimate at σ→0,
a product identity, or an averaged bound on collision primes. -/
theorem fixed_regulator_summable
    (W : ℕ) (a : I→ℤ) (b : I→ℕ) (hU : ∀ i,W.Coprime (b i))
    (σ : ℝ) (hσ : 0<σ) (s u : I→ℂ) (hs : ∀ i,σ≤(s i).re) (hu : ∀ i,σ≤(u i).re) :
    Summable (primeAbsoluteBudget W a b s u) := by
  let C : ℝ := ((2:ℝ)^Fintype.card I)^2
  have h : Summable (fun n : ℕ => C*(n:ℝ)^(-1-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -1-σ<(-1:ℝ))).mul_left C
  have hp : Summable (fun n : {p : ℕ // p.Prime} => C*(n.val:ℝ)^(-1-σ)) :=
    h.comp_injective Subtype.val_injective
  apply hp.of_norm_bounded
  intro p
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  have hn : 0≤primeAbsoluteBudget W a b s u p := by
    unfold primeAbsoluteBudget
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_of_nonneg hn]
  exact fixed_regulator_budget W p.val p.property a b hU σ hσ s u hs hu

end ActualTZRegulatedPhysicalBounds318
