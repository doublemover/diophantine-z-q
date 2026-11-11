module
public import ThreeDetectorArithmetic318
public import HTail318
public section
noncomputable section
namespace PadicDetectorCoefficients318
open CircuitReplay DetectorWeightPreparation318
open Set
open scoped Topology
set_option maxHeartbeats 1000000

/-- Actual finite coefficient inputs, now in their p-adic coordinate topology.
This does not put the real topology on the rational input coefficients. -/
abbrev Coeff (F : Type*) := Fin 146 → F
@[expose] def project (p : ℕ) [Fact p.Prime] (w : Assignment) : Coeff ℚ_[p] :=
  fun i => (w i.val:ℚ_[p])

/-- The same original sixteen unweighted leaf pairs over an arbitrary ring. -/
@[expose] def values {F : Type*} [CommRing F] (w : Coeff F) : Fin 16 → F × F :=
  ![(w 126,0),
    (w 125,0),
    (w 58,2*w 59),
    (w 60,2*w 61),
    (2*w 62,2*w 63),
    (w 64,2*w 65),
    (w 19-1,-w 20),
    (w 23-1,-w 24),
    (w 27-1,-w 28),
    (w 31-1,-w 32),
    (w 127,2*w 128),
    (w 129,2*w 130),
    (w 131,2*w 132),
    (w 133,2*w 134),
    (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729,-7446*w 103-29784*w 136),
    (-2*w 123+w 137+1,-4*w 124+4*w 138)]

lemma values_continuous {F : Type*} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F] :
    Continuous (values (F:=F)) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp [values] <;> fun_prop

lemma rational_embedding (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ConcretePadic318.rationalPlace p q=Padic.addValuation (q:ℚ_[p]) := by
  by_cases hq : q=0
  · simp [hq]
  · rw [ConcretePadic318.rational_value p q hq,
      Padic.addValuation.apply (Rat.cast_ne_zero.mpr hq),Padic.valuation_ratCast]

/-- Every actual rational leaf coefficient is exactly one of the p-adic
polynomial values; no arbitrary replacement coefficient is involved. -/
lemma member_values (p : ℕ) [Fact p.Prime] (w : Assignment)
    (a : Fin 3 × ConcreteG8Domain.K) (ha : a∈coefficients w) :
    ∃ j : Fin 16, ((a.2.re:ℚ_[p]),(a.2.im:ℚ_[p]))=values (project p w) j := by
  simp only [coefficients,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha|ha
  · subst a
    refine ⟨0,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨1,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨2,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨3,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨4,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨5,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨6,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨7,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨8,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨9,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨10,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨11,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨12,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨13,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨14,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring
  · subst a
    refine ⟨15,?_⟩
    norm_num [values,project,ConcreteG8Domain.pair] <;> push_cast <;> ring

lemma lower_bound (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ∃ B : ℤ, (B:WithTop ℤ)≤Padic.addValuation x := by
  by_cases hx : x=0
  · exact ⟨0,by simp [hx]⟩
  · exact ⟨x.valuation,by rw [Padic.addValuation.apply hx]⟩

/-- Polynomial continuity constructs an actual nonempty p-adic neighborhood
with one lower bound for all original coefficients. The center may be any
p-adic coefficient vector, not merely a sampled rational point. -/
theorem neighborhood (p : ℕ) [Fact p.Prime] (x₀ : Coeff ℚ_[p]) :
    ∃ U : Set (Coeff ℚ_[p]), IsOpen U ∧ x₀∈U ∧
      ∃ B : ℤ, B≤0 ∧ ∀ x∈U, ∀ j : Fin 16,
        (B:WithTop ℤ)≤Padic.addValuation (values x j).1 ∧
        (B:WithTop ℤ)≤Padic.addValuation (values x j).2 := by
  have he : ∀ j : Fin 16, ∃ B : ℤ,
      (B:WithTop ℤ)≤Padic.addValuation (values x₀ j).1 ∧
      (B:WithTop ℤ)≤Padic.addValuation (values x₀ j).2 := by
    intro j
    obtain ⟨Br,hr⟩ := lower_bound p (values x₀ j).1
    obtain ⟨Bi,hi⟩ := lower_bound p (values x₀ j).2
    exact ⟨min Br Bi,le_trans (by exact_mod_cast min_le_left Br Bi) hr,
      le_trans (by exact_mod_cast min_le_right Br Bi) hi⟩
  choose Bj hBj using he
  let B : ℤ := -(∑ j : Fin 16, |Bj j|)
  have hB0 : B≤0 := by dsimp [B]; exact neg_nonpos.mpr (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hBj' (j : Fin 16) : B≤Bj j := by
    have hs := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => abs_nonneg (Bj i)) (Finset.mem_univ j)
    exact le_trans (neg_le_neg hs) (neg_abs_le (Bj j))
  let U : Set (Coeff ℚ_[p]) := {x | ∀ j : Fin 16,
    ‖(values x j).1-(values x₀ j).1‖<1 ∧ ‖(values x j).2-(values x₀ j).2‖<1}
  have hopen : IsOpen U := by
    change IsOpen (⋂ j : Fin 16, {x | ‖(values x j).1-(values x₀ j).1‖<1 ∧
      ‖(values x j).2-(values x₀ j).2‖<1})
    apply isOpen_iInter_of_finite
    intro j
    have hc := (continuous_apply j).comp (values_continuous (F:=ℚ_[p]))
    exact (isOpen_lt (hc.fst.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (hc.snd.sub continuous_const).norm continuous_const)
  refine ⟨U,hopen,by simp [U],B,hB0,?_⟩
  intro x hx j
  have key (a b : ℚ_[p]) (hab : ‖a-b‖<1)
      (hb : (B:WithTop ℤ)≤Padic.addValuation b) :
      (B:WithTop ℤ)≤Padic.addValuation a := by
    have hdiff : (0:WithTop ℤ)≤Padic.addValuation (a-b) :=
      (HTail318.norm_le_iff_valuation p (a-b) 0).mp (by simpa using le_of_lt hab)
    have hsum := Padic.addValuation.map_add (a-b) b
    rw [sub_add_cancel] at hsum
    exact le_trans (le_min (le_trans (by exact_mod_cast hB0) hdiff) hb) hsum
  exact ⟨key _ _ (hx j).1 (le_trans (by exact_mod_cast hBj' j) (hBj j).1),
    key _ _ (hx j).2 (le_trans (by exact_mod_cast hBj' j) (hBj j).2)⟩

/-- Concrete rational coefficient arrays in that neighborhood have the same
uniform bound on every original unweighted detector leaf. -/
theorem actual_neighborhood (p : ℕ) [Fact p.Prime] (w₀ : Assignment) :
    ∃ U : Set (Coeff ℚ_[p]), IsOpen U ∧ project p w₀∈U ∧
      ∃ B : ℤ, B≤0 ∧ ∀ w : Assignment, project p w∈U →
        ∀ a∈coefficients w,
          (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.re ∧
          (B:WithTop ℤ)≤ConcretePadic318.rationalPlace p a.2.im := by
  obtain ⟨U,hU,hcenter,B,hB0,hB⟩ := neighborhood p (project p w₀)
  refine ⟨U,hU,hcenter,B,hB0,?_⟩
  intro w hw a ha
  obtain ⟨j,hj⟩ := member_values p w a ha
  have hb := hB (project p w) hw j
  rw [←hj] at hb
  simpa only [rational_embedding] using hb

end PadicDetectorCoefficients318
