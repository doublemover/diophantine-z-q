module
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public section
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace IntegralRingEvaluation318
open PowerSeries Filter
open scoped Topology
/-- The unit-ball ring interface needed by closed-disc evaluation. -/
class NormBoundOne (R : Type*) [NormedCommRing R] : Prop where
  norm_le_one : ∀ x : R, ‖x‖ ≤ 1

variable (R : Type*) [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R]
  [NormBoundOne R]

instance nonarchimedeanRing : NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- Restrictedness in the actual topology of a complete integral normed ring. -/
abbrev Restricted (f : PowerSeries R) : Prop := IsRestricted 1 f

/-- Actual monomial sum, also at unit arguments. -/
@[expose] noncomputable def eval (f : PowerSeries R) (t : R) : R :=
  ∑' n : ℕ, coeff n f * t^n

theorem coefficient_tendsto (f : PowerSeries R) (hf : Restricted R f) :
    Tendsto (fun n => coeff n f) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [one_pow, mul_one] using (isRestricted_iff' 1 f).1 hf

theorem summable_of_norm_le {ι : Type*} (a b : ι → R)
    (ha : Summable a) (hb : ∀ i, ‖b i‖ ≤ ‖a i‖) : Summable b := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  exact squeeze_zero (fun i => norm_nonneg _) hb (by simpa using ha.tendsto_cofinite_zero.norm)

theorem monomial_summable (f : PowerSeries R) (hf : Restricted R f) (t : R) :
    Summable (fun n => coeff n f * t^n) := by
  apply summable_of_norm_le R (fun n => coeff n f)
  · apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using coefficient_tendsto R f hf
  · intro n
    exact (norm_mul_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one (t^n)))

theorem eval_hasSum (f : PowerSeries R) (hf : Restricted R f) (t : R) :
    HasSum (fun n => coeff n f * t^n) (eval R f t) :=
  (monomial_summable R f hf t).hasSum

theorem eval_norm (f : PowerSeries R) (t : R) : ‖eval R f t‖ ≤ 1 :=
  NormBoundOne.norm_le_one _

/-- A double family with small outer rows and convergent individual rows is summable.
The integral coefficient bound is uniform in the inner index. -/
theorem double_summable (a : ℕ → R) (ha : Summable a) (F : ℕ × ℕ → R)
    (hr : ∀ n, Summable (fun m => F (n,m)))
    (hb : ∀ n m, ‖F (n,m)‖ ≤ ‖a n‖) : Summable F := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply Metric.tendsto_nhds.2
  intro ε hε
  apply eventually_cofinite.2
  have hrows : {n | ¬ dist (a n) 0 < ε}.Finite :=
    eventually_cofinite.1 (Metric.tendsto_nhds.1 ha.tendsto_cofinite_zero ε hε)
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply hrows.subset
    rintro n ⟨⟨i,j⟩, hij, rfl⟩ hn
    apply hij
    simpa only [dist_zero_right] using lt_of_le_of_lt (hb i j) (by simpa only [dist_zero_right] using hn)
  · intro n hn
    have hrow : {m | ¬ dist (F (n,m)) 0 < ε}.Finite :=
      eventually_cofinite.1 (Metric.tendsto_nhds.1 (hr n).tendsto_cofinite_zero ε hε)
    apply (hrow.image (fun m => (n,m))).subset
    rintro ⟨i,j⟩ ⟨hij, he⟩
    have hin : i=n := he
    subst i
    exact ⟨j,hij,rfl⟩



set_option backward.isDefEq.respectTransparency false in
theorem eval_mul (f g : PowerSeries R) (hf : Restricted R f) (hg : Restricted R g)
    (t : R) : eval R (f*g) t = eval R f t * eval R g t := by
  have hfs := monomial_summable R f hf t
  have hgs := monomial_summable R g hg t
  have hprod : Summable (fun z : ℕ × ℕ =>
      (coeff z.1 f * t^z.1) * (coeff z.2 g * t^z.2)) := by
    apply double_summable R _ hfs
    · intro n
      exact hgs.mul_left (coeff n f * t^n)
    · intro n m
      exact (norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _))
  have hh : (∑' n : ℕ, coeff n f*t^n) * (∑' n : ℕ, coeff n g*t^n) =
      ∑' n : ℕ, ∑ z ∈ Finset.antidiagonal n,
        (coeff z.1 f*t^z.1)*(coeff z.2 g*t^z.2) :=
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hfs hgs hprod
  dsimp only [eval]
  rw [hh]
  apply tsum_congr
  intro n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' := Finset.mem_antidiagonal.mp hz
  rw [←hz', pow_add]
  ring

@[simp] theorem eval_one (t : R) : eval R 1 t = 1 := by
  simp [eval, coeff_one]

theorem eval_pow (f : PowerSeries R) (hf : Restricted R f) (t : R) (n : ℕ) :
    eval R (f^n) t = (eval R f t)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, eval_mul R _ _ (hf.pow n) hf, ih, pow_succ]

/-- The genuine double coefficient family for formal composition converges
unconditionally, including evaluation at every unit of the integral ring. -/
theorem composition_family_summable (f g : PowerSeries R)
    (hf : Restricted R f) (hg : Restricted R g) (t : R) :
    Summable (fun z : ℕ × ℕ => coeff z.1 f * coeff z.2 (g^z.1) * t^z.2) := by
  have hfc : Summable (fun n => coeff n f) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using coefficient_tendsto R f hf
  apply double_summable R (fun n => coeff n f) hfc
  · intro n
    simpa only [mul_assoc] using (monomial_summable R (g^n) (hg.pow n) t).mul_left (coeff n f)
  · intro n m
    calc
      _ ≤ (‖coeff n f‖ * ‖coeff m (g^n)‖) * ‖t^m‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖coeff n f‖ * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (NormBoundOne.norm_le_one _) (norm_nonneg _))
        (NormBoundOne.norm_le_one _) (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem composition_column (f g : PowerSeries R) (hg0 : constantCoeff g=0)
    (t : R) (m : ℕ) :
    ∑' n : ℕ, coeff n f * coeff m (g^n) * t^m = coeff m (f.subst g)*t^m := by
  have hs : HasSubst g := .of_constantCoeff_zero hg0
  have hfinite := coeff_subst_finite' hs f m
  have hsum : Summable (fun n => coeff n f * coeff m (g^n)) := by
    simpa only [smul_eq_mul] using
      (summable_of_hasFiniteSupport hfinite : Summable (fun n => coeff n f • coeff m (g^n)))
  rw [hsum.tsum_mul_right (t^m), coeff_subst' hs,
    ←tsum_eq_finsum (L := .unconditional ℕ) hfinite]
  simp only [smul_eq_mul]

/-- Summability of the actual coefficients of the substituted series at any integral argument. -/
theorem subst_summable (f g : PowerSeries R)
    (hf : Restricted R f) (hg : Restricted R g) (hg0 : constantCoeff g=0) (t : R) :
    Summable (fun m : ℕ => coeff m (f.subst g)*t^m) := by
  have hs := (composition_family_summable R f g hf hg t).prod_symm.prod
  simpa only [Prod.swap_prod_mk, composition_column R f g hg0 t] using hs

/-- Formal substitution of restricted integral series remains restricted. -/
theorem subst_restricted (f g : PowerSeries R)
    (hf : Restricted R f) (hg : Restricted R g) (hg0 : constantCoeff g=0) :
    Restricted R (f.subst g) := by
  apply (isRestricted_iff' 1 _).2
  have hs := (subst_summable R f g hf hg hg0 1).tendsto_atTop_zero.norm
  simpa only [one_pow, mul_one, norm_zero] using hs

/-- Actual closed-unit-disc evaluation commutes with formal composition.
No analytic composition or logarithm law is assumed. -/
theorem eval_subst (f g : PowerSeries R)
    (hf : Restricted R f) (hg : Restricted R g) (hg0 : constantCoeff g=0) (t : R) :
    eval R (f.subst g) t = eval R f (eval R g t) := by
  have hs := composition_family_summable R f g hf hg t
  calc
    eval R (f.subst g) t = ∑' m : ℕ, ∑' n : ℕ, coeff n f * coeff m (g^n) * t^m := by
      apply tsum_congr
      intro m
      exact (composition_column R f g hg0 t m).symm
    _ = ∑' n : ℕ, ∑' m : ℕ, coeff n f * coeff m (g^n) * t^m := by
      exact Summable.tsum_comm (f := fun n m => coeff n f * coeff m (g^n) * t^m) hs
    _ = eval R f (eval R g t) := by
      apply tsum_congr
      intro n
      rw [show (fun m => coeff n f * coeff m (g^n) * t^m) =
          (fun m => coeff n f * (coeff m (g^n) * t^m)) from funext (fun m => mul_assoc _ _ _),
        (monomial_summable R (g^n) (hg.pow n) t).tsum_mul_left (coeff n f)]
      change coeff n f * eval R (g^n) t = _
      rw [eval_pow R g hg t]


@[simp] theorem eval_X (t : R) : eval R X t = t := by
  simp [eval, coeff_X]

@[simp] theorem eval_C (c t : R) : eval R (C c) t = c := by
  simp [eval, coeff_C]

theorem eval_neg (f : PowerSeries R) (t : R) :
    eval R (-f) t = -eval R f t := by
  simp only [eval, map_neg, neg_mul, tsum_neg]

theorem eval_add (f g : PowerSeries R) (hf : Restricted R f) (hg : Restricted R g)
    (t : R) : eval R (f+g) t = eval R f t + eval R g t := by
  simp only [eval, map_add, add_mul]
  exact (monomial_summable R f hf t).tsum_add (monomial_summable R g hg t)

theorem eval_sub (f g : PowerSeries R) (hf : Restricted R f) (hg : Restricted R g)
    (t : R) : eval R (f-g) t = eval R f t - eval R g t := by
  rw [sub_eq_add_neg, eval_add R _ _ hf hg.neg, eval_neg, sub_eq_add_neg]


/-- Isometric coefficient inclusions preserve the actual closed-disc restrictedness. -/
theorem restricted_map {S : Type*} [NormedCommRing S] (φ : R →+* S)
    (hφ : Isometry φ) (f : PowerSeries R) (hf : Restricted R f) :
    IsRestricted 1 (PowerSeries.map φ f) := by
  apply (isRestricted_iff' 1 _).2
  have hn (x : R) : ‖φ x‖=‖x‖ := by
    simpa only [map_zero, dist_zero_right] using hφ.dist_eq x 0
  simpa only [coeff_map, hn] using (isRestricted_iff' 1 f).1 hf

theorem X_restricted : Restricted R (X : PowerSeries R) :=
  MvPowerSeries.isRestricted_X (fun _ => 1) ()

/-- Integral rescaling preserves restrictedness even when the parameter is a unit. -/
theorem rescale_restricted (a : R) (f : PowerSeries R) (hf : Restricted R f) :
    Restricted R (rescale a f) := by
  apply (isRestricted_iff' 1 _).2
  simp only [one_pow, mul_one]
  have ht := (coefficient_tendsto R f hf).norm
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) (by simpa only [norm_zero] using ht)
  rw [coeff_rescale]
  exact (norm_mul_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (NormBoundOne.norm_le_one _))

end IntegralRingEvaluation318
#print axioms IntegralRingEvaluation318.eval_mul
#print axioms IntegralRingEvaluation318.eval_pow
#print axioms IntegralRingEvaluation318.double_summable

#print axioms IntegralRingEvaluation318.eval_subst
#print axioms IntegralRingEvaluation318.subst_restricted

#print axioms IntegralRingEvaluation318.restricted_map
