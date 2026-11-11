module
public import DetectorSmallPrimePreparation318
public section
noncomputable section
namespace DetectorWeightPreparation318
open CircuitReplay ConcreteG8Domain ActualDetectorFold318
open ScaledContactWeights318 ScaledDetectorChain318 DetectorPrimeProduct318
open DetectorSmallPrimePreparation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- Only the original coefficient pairs are listed; all have indices<146.
The tag selects the actual q1,q4,q13 source weight. -/
@[expose] def coefficients (w : Assignment) : List (Fin 3 × K) :=
  [(1,pair (w 126) (0)),
   (0,pair (w 125) (0)),
   (0,pair (w 58) (2*w 59)),
   (0,pair (w 60) (2*w 61)),
   (0,pair (2*w 62) (2*w 63)),
   (0,pair (w 64) (2*w 65)),
   (0,pair (w 19-1) (-w 20)),
   (0,pair (w 23-1) (-w 24)),
   (0,pair (w 27-1) (-w 28)),
   (0,pair (w 31-1) (-w 32)),
   (1,pair (w 127) (2*w 128)),
   (2,pair (w 129) (2*w 130)),
   (2,pair (w 131) (2*w 132)),
   (2,pair (w 133) (2*w 134)),
   (1,pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)),
   (2,pair (-2*w 123+w 137+1) (-4*w 124+4*w 138))]

@[expose] def weights (c t : ℚ) : Fin 3 → ℚ :=
  ![scaledWeight c t,(scaledWeight c t)^7*(delta c t)^18,
    (scaledWeight c t)^25*(delta c t)^72]

lemma leaves_weights (w : Assignment) (c t : ℚ) :
    leaves (view w c t)=
      (coefficients w).map (fun a => (pair (weights c t a.1) 0,a.2)) := by
  norm_num [leaves,view,ContactChainLimits318.view,coefficients,weights]

/-- The exact three weight valuations, with their original7/25 powers and
18/72 delta powers. This uses the same integer contact product. -/
theorem weight_values (p : ℕ) [Fact p.Prime] (c u d : ℚ)
    (hc : c≠0) (hd : d≠0) (k : Fin 5 → ℤ)
    (hk : ∀ j, linear c u d j=(k j:ℚ)) (hkn : ∀ j, k j≠0)
    (hku : ∀ j, padicValRat p (k j:ℚ)=0)
    (hdeep : padicValRat p c<padicValRat p d) :
    (∀ j, weights c (u/d^2) j≠0) ∧
    padicValRat p (weights c (u/d^2) 0)=6*padicValRat p d+4*padicValRat p c ∧
    padicValRat p (weights c (u/d^2) 1)=6*padicValRat p d+64*padicValRat p c ∧
    padicValRat p (weights c (u/d^2) 2)=6*padicValRat p d+244*padicValRat p c := by
  have hu : u=(k 0:ℚ) := by simpa [linear,theta] using hk 0
  have hu0 : u≠0 := by rw [hu]; exact_mod_cast hkn 0
  have huv : padicValRat p u=0 := by rw [hu]; exact hku 0
  obtain ⟨hdelta,hdel⟩ := delta_value p c u d hc hu0 hd huv hdeep
  have hF : ContactWeightWitness318.contact (parameter c (u/d^2))=
      c^10/d^10*(product k:ℚ) := by
    rw [contact_product c u d hc hd,hk 0,hk 1,hk 2,hk 3,hk 4,product_cast]
  have hN : (product k:ℚ)≠0 := by exact_mod_cast product_ne k hkn
  have hF0 : ContactWeightWitness318.contact (parameter c (u/d^2))≠0 := by
    rw [hF]; exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hd)) hN
  have hFval : padicValRat p (ContactWeightWitness318.contact (parameter c (u/d^2)))=
      10*padicValRat p c-10*padicValRat p d := by
    rw [hF,padicValRat.mul (div_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hd)) hN,
      padicValRat.div (pow_ne_zero _ hc) (pow_ne_zero _ hd),padicValRat.pow,padicValRat.pow,
      product_unit p k hkn hku]
    norm_num
  have hq : scaledWeight c (u/d^2)≠0 :=
    mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hdelta) hF0)
  have hqval : padicValRat p (scaledWeight c (u/d^2))=
      6*padicValRat p d+4*padicValRat p c := by
    change padicValRat p (c^10*((delta c (u/d^2))^2/ContactWeightWitness318.contact (parameter c (u/d^2))))=_
    rw [padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hdelta) hF0),
      padicValRat.div (pow_ne_zero _ hdelta) hF0,padicValRat.pow,padicValRat.pow,hFval]
    change _+(_*padicValRat p (delta c (u/d^2))-_)=_
    rw [hdel]
    norm_num <;> ring
  refine ⟨?_,hqval,?_,?_⟩
  · intro j
    fin_cases j
    · exact hq
    · exact mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hdelta)
    · exact mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hdelta)
  · change padicValRat p ((scaledWeight c (u/d^2))^7*(delta c (u/d^2))^18)=_
    rw [padicValRat.mul (pow_ne_zero _ hq) (pow_ne_zero _ hdelta),
      padicValRat.pow,padicValRat.pow,hqval,hdel]
    norm_num <;> ring
  · change padicValRat p ((scaledWeight c (u/d^2))^25*(delta c (u/d^2))^72)=_
    rw [padicValRat.mul (pow_ne_zero _ hq) (pow_ne_zero _ hdelta),
      padicValRat.pow,padicValRat.pow,hqval,hdel]
    norm_num <;> ring

lemma rational_lower (p : ℕ) [Fact p.Prime] (x : ℚ) :
    ∃ B : ℤ, (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p x := by
  by_cases hx : x=0
  · exact ⟨0,by simp [hx]⟩
  · exact ⟨padicValRat p x,by rw [ConcretePadic318.rational_value p x hx]⟩

lemma finite_lower (p : ℕ) [Fact p.Prime] (xs : List (Fin 3 × K)) :
    ∃ B : ℤ, ∀ a∈xs,
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.re ∧
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.im := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons a xs ih =>
    obtain ⟨Br,hr⟩ := rational_lower p a.2.re
    obtain ⟨Bi,hi⟩ := rational_lower p a.2.im
    obtain ⟨B,hB⟩ := ih
    refine ⟨min (min Br Bi) B,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with he|he
    · subst b
      constructor
      · exact le_trans (by exact_mod_cast le_trans (min_le_left (min Br Bi) B) (min_le_left Br Bi)) hr
      · exact le_trans (by exact_mod_cast le_trans (min_le_left (min Br Bi) B) (min_le_right Br Bi)) hi
    · exact ⟨le_trans (by exact_mod_cast min_le_right (min Br Bi) B) (hB b he).1,
        le_trans (by exact_mod_cast min_le_right (min Br Bi) B) (hB b he).2⟩

/-- A finite lower bound exists for the actual source coefficients, before
choosing the common parameter denominator. Zero coefficients are harmless. -/
theorem actual_coefficient_bound (p : ℕ) [Fact p.Prime] (w : Assignment) :
    ∃ B : ℤ, ∀ a∈coefficients w,
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.re ∧
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.im :=
  finite_lower p (coefficients w)

lemma weighted_depths (p : ℕ) [Fact p.Prime] (w : Assignment) (c t : ℚ) (B : ℤ)
    (hB : ∀ a∈coefficients w,
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.re ∧
      (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.im)
    (hq : ∀ j, weights c t j≠0)
    (hv : ∀ j, -B<padicValRat p (weights c t j)) :
    ∀ a∈leaves (view w c t),
      0<ConcretePadic318.rationalPlace p (a.1*a.2).re ∧
      0<ConcretePadic318.rationalPlace p (a.1*a.2).im := by
  intro a ha
  rw [leaves_weights] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have he (x : ℚ) (hx : (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p x) :
      0<ConcretePadic318.rationalPlace p (weights c t b.1*x) := by
    rw [(ConcretePadic318.rationalPlace p).map_mul,ConcretePadic318.rational_value p _ (hq b.1)]
    have hpos : (0:WithTop ℤ)<(padicValRat p (weights c t b.1):WithTop ℤ)+(B:WithTop ℤ) := by
      exact_mod_cast (show 0<padicValRat p (weights c t b.1)+B by have := hv b.1; omega)
    exact lt_of_lt_of_le hpos (add_le_add_left hx _)
  constructor
  · simpa [pair] using he b.2.re (hB b hb).1
  · simpa [pair] using he b.2.im (hB b hb).2

/-- Arbitrarily large local divisibility of d makes every actual weighted
leaf small, with an explicit threshold fixed by the coefficient bound and c. -/
theorem eventual_leaf_depths (p : ℕ) [Fact p.Prime] (w : Assignment) (c : ℚ) (hc : c≠0) :
    ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ (k : Fin 5 → ℤ), (∀ j, linear c u d j=(k j:ℚ)) →
      (∀ j, k j≠0) → (∀ j, padicValRat p (k j:ℚ)=0) →
      ∀ a∈leaves (view w c (u/d^2)),
        0<ConcretePadic318.rationalPlace p (a.1*a.2).re ∧
        0<ConcretePadic318.rationalPlace p (a.1*a.2).im := by
  obtain ⟨B,hB⟩ := actual_coefficient_bound p w
  refine ⟨|B|+244*|padicValRat p c|+1,?_⟩
  intro u d hd hN k hk hkn hku
  have hB₁ := le_abs_self B
  have hB₂ := neg_le_abs B
  have hc₁ := le_abs_self (padicValRat p c)
  have hc₂ := neg_le_abs (padicValRat p c)
  have hdeep : padicValRat p c<padicValRat p d := by omega
  obtain ⟨hq,h0,h1,h2⟩ := weight_values p c u d hc hd k hk hkn hku hdeep
  apply weighted_depths p w c (u/d^2) B hB hq
  intro j
  fin_cases j
  · change -B<padicValRat p (weights c (u/d^2) 0)
    rw [h0]; omega
  · change -B<padicValRat p (weights c (u/d^2) 1)
    rw [h1]; omega
  · change -B<padicValRat p (weights c (u/d^2) 2)
    rw [h2]; omega

end DetectorWeightPreparation318
