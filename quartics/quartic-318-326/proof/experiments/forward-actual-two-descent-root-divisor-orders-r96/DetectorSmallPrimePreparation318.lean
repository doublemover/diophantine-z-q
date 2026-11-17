module
public import DetectorDenominatorPreparation318
public import ActualDetectorPairDepth318
public section
noncomputable section
namespace DetectorSmallPrimePreparation318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318 DetectorPrimeProduct318
open DetectorDenominatorPreparation318 ActualDetectorFold318
set_option maxHeartbeats 1000000

lemma traceQuotient_ne (w : Assignment) (c t : ℚ) (hr : realChain w c t≠0) :
    traceQuotient w c t≠0 := by
  have hx : ConcreteG8Domain.pair (realChain w c t) (imagChain w c t)≠0 := by
    intro he
    exact hr (congrArg QuadraticAlgebra.re he)
  have hn : (realChain w c t)^2-2*(imagChain w c t)^2≠0 := by
    simpa only [AnchorNorm318.norm_pair] using AnchorNorm318.norm_ne_zero hx
  exact div_ne_zero hn (mul_ne_zero (by norm_num) hr)

lemma product_unit (p : ℕ) [Fact p.Prime] (k : Fin 5 → ℤ)
    (hk : ∀ j, k j≠0) (hu : ∀ j, padicValRat p (k j:ℚ)=0) :
    padicValRat p (product k:ℚ)=0 := by
  rw [product_cast]
  have hn (j : Fin 5) : (k j:ℚ)≠0 := by exact_mod_cast hk j
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3)) (hn 4),
    padicValRat.mul (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3),
    padicValRat.mul (mul_ne_zero (hn 0) (hn 1)) (hn 2),padicValRat.mul (hn 0) (hn 1),
    hu 0,hu 1,hu 2,hu 3,hu 4]
  norm_num

/-- At a small prime, a locally deep common square denominator dominates
both the fixed root scale and the subtraction of1 in the actual delta. -/
lemma delta_value (p : ℕ) [Fact p.Prime] (c u d : ℚ)
    (hc : c≠0) (hu : u≠0) (hd : d≠0) (huv : padicValRat p u=0)
    (hdeep : padicValRat p c<padicValRat p d) :
    delta c (u/d^2)≠0 ∧
      padicValRat p (delta c (u/d^2))=2*padicValRat p c-2*padicValRat p d := by
  have hA : parameter c (u/d^2)≠0 :=
    mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero hu (pow_ne_zero _ hd))
  have hvA : padicValRat p (parameter c (u/d^2))=2*padicValRat p c-2*padicValRat p d := by
    rw [parameter,padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero hu (pow_ne_zero _ hd)),
      padicValRat.pow,padicValRat.div hu (pow_ne_zero _ hd),padicValRat.pow,huv]
    norm_num <;> ring
  have hdelta : delta c (u/d^2)≠0 := by
    intro hz
    have he : parameter c (u/d^2)=1 := by unfold delta at hz; linarith
    rw [he] at hvA
    simp only [padicValRat.one] at hvA
    omega
  refine ⟨hdelta,?_⟩
  change padicValRat p (parameter c (u/d^2)-1)=_
  have hsum : parameter c (u/d^2)+(-1)≠0 := by simpa only [delta,sub_eq_add_neg] using hdelta
  rw [sub_eq_add_neg,padicValRat.add_eq_of_lt hsum hA (by norm_num) (by rw [hvA]; norm_num; omega),hvA]

/-- Exact small-prime value of the original pole, after the actual chain's
component depths have produced its inverse trace. No trace-unit input is assumed. -/
theorem pole_value (p : ℕ) [Fact p.Prime] (w : Assignment) (c u d : ℚ)
    (hc : c≠0) (hd : d≠0) (k : Fin 5 → ℤ)
    (hk : ∀ j, linear c u d j=(k j:ℚ)) (hkn : ∀ j, k j≠0)
    (hku : ∀ j, padicValRat p (k j:ℚ)=0)
    (hdeep : padicValRat p c<padicValRat p d)
    (hleaf : ∀ a∈leaves (view w c (u/d^2)),
      0<ConcretePadic318.rationalPlace p (a.1*a.2).re ∧
      0<ConcretePadic318.rationalPlace p (a.1*a.2).im) :
    realChain w c (u/d^2)≠0 ∧ poleInput w c (u/d^2)≠0 ∧
      padicValRat p (poleInput w c (u/d^2))=
        2*padicValRat p d-12*padicValRat p c-2*padicValRat p (2:ℚ) := by
  have hu : u=(k 0:ℚ) := by simpa [linear,theta] using hk 0
  have hu0 : u≠0 := by rw [hu]; exact_mod_cast hkn 0
  have huv : padicValRat p u=0 := by rw [hu]; exact hku 0
  obtain ⟨hdelta,hdel⟩ := delta_value p c u d hc hu0 hd huv hdeep
  obtain ⟨ha,hqv⟩ := ActualDetectorPairDepth318.quotient_value p (view w c (u/d^2)) hleaf
  change realChain w c (u/d^2)≠0 at ha
  change padicValRat p (traceQuotient w c (u/d^2))= -padicValRat p (2:ℚ) at hqv
  have hq := traceQuotient_ne w c (u/d^2) ha
  have hz : DetectorPrimeProduct318.squareFactor w c u d≠0 :=
    div_ne_zero hq (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hdelta))
  have hN : (product k:ℚ)≠0 := by exact_mod_cast product_ne k hkn
  have hb : poleInput w c (u/d^2)≠0 := by
    rw [pole_product w c u d hc hd k hk]
    exact mul_ne_zero hN (pow_ne_zero _ hz)
  refine ⟨ha,hb,?_⟩
  rw [pole_product w c u d hc hd k hk,padicValRat.mul hN (pow_ne_zero _ hz),
    product_unit p k hkn hku,padicValRat.pow,
    squareFactor_value p w c u d hq hd hdelta,hqv,hdel]
  norm_num <;> ring

end DetectorSmallPrimePreparation318
