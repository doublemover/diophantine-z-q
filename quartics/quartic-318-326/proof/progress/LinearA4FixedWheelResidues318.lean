module
public import LinearA4ObservedResidues318
public import Mathlib.Algebra.Field.ZMod
import all LinearA4ObservedResidues318
public section
noncomputable section

/-! Exact fixed-wheel specialization of the observed Gaussian residue count.
The extra fixed ray and ramification factors are allowed as multiples of the
wheel below. No moving conductor, joint prime event, or distribution estimate
is assumed by the finite statement. -/
namespace LinearA4FixedWheelResidues318
open LinearA4ObservedResidues318 LinearA4EulerDensity318
open LinearA4GaussianCounts318 LinearA4MixedNormCounts318
open scoped BigOperators

/-- Only the prime q receives the none label. These are the original
rescaled readings, not the homogeneous quadratic readings u+kQ²q². -/
def originalForm (Q u q : ℤ) : Option ℤ → ℤ
  | none => q
  | some k => u+k*Q^2*q

def labelReduce (p : ℕ) : Option ℤ → Option (ZMod p)
  | none => none
  | some k => some (k:ZMod p)

/-- Leave out the diagonal, and the at most one none label. Ordered pairs
are convenient and duplicating a factor does not change the omitted primes. -/
def slopeFactor {σ : Type*} [DecidableEq σ] (slots : σ → Option ℤ)
    (ij : σ × σ) : ℤ :=
  if ij.1=ij.2 then 1 else
    match slots ij.1, slots ij.2 with
    | some a, some b => b-a
    | _, _ => 1

def wheel {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : ℤ)
    (slots : σ → Option ℤ) : ℤ :=
  (2*Q) * ∏ ij : σ × σ, slopeFactor slots ij

theorem wheel_ne_zero {σ : Type*} [Fintype σ] [DecidableEq σ] {Q : ℤ}
    (hQ : Q≠0) {slots : σ → Option ℤ} (hinj : Function.Injective slots) :
    wheel Q slots≠0 := by
  unfold wheel
  refine mul_ne_zero (mul_ne_zero (by norm_num) hQ) (Finset.prod_ne_zero_iff.mpr ?_)
  rintro ⟨i,j⟩ -
  by_cases hij : i=j
  · simp [slopeFactor,hij]
  · rcases ha : slots i with _|a <;> rcases hb : slots j with _|b <;>
      simp [slopeFactor,hij,ha,hb]
    exact fun e => hij (hinj (by rw [ha,hb,sub_eq_zero.mp e]))

theorem two_dvd_wheel {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : ℤ)
    (slots : σ → Option ℤ) : (2:ℤ)∣wheel Q slots := by
  refine ⟨Q * ∏ ij : σ × σ, slopeFactor slots ij,?_⟩
  unfold wheel
  ring

theorem Q_dvd_wheel {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : ℤ)
    (slots : σ → Option ℤ) : Q∣wheel Q slots := by
  refine ⟨2 * ∏ ij : σ × σ, slopeFactor slots ij,?_⟩
  unfold wheel
  ring

theorem slope_dvd_wheel {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : ℤ)
    (slots : σ → Option ℤ) {i j : σ} (hij : i≠j)
    {a b : ℤ} (ha : slots i=some a) (hb : slots j=some b) :
    b-a∣wheel Q slots := by
  have h := Finset.dvd_prod_of_mem (slopeFactor slots)
    (Finset.mem_univ (i,j))
  have hf : slopeFactor slots (i,j)=b-a := by simp [slopeFactor,hij,ha,hb]
  rw [hf] at h
  obtain ⟨c,hc⟩ := h
  refine ⟨(2*Q)*c,?_⟩
  unfold wheel
  rw [hc]
  ring

theorem good_reduction {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : ℕ) (Q M : ℤ) (slots : σ → Option ℤ) (hinj : Function.Injective slots)
    (hm : wheel Q slots∣M) (hp : ¬(p:ℤ)∣M) :
    p≠2 ∧ (Q:ZMod p)≠0 ∧ Function.Injective (fun i => labelReduce p (slots i)) := by
  refine ⟨?_,?_,?_⟩
  · rintro rfl
    exact hp ((two_dvd_wheel Q slots).trans hm)
  · intro hz
    exact hp (((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mp hz).trans
      ((Q_dvd_wheel Q slots).trans hm))
  · intro i j e
    by_contra hij
    rcases ha : slots i with _|a <;> rcases hb : slots j with _|b
    · exact hij (hinj (ha.trans hb.symm))
    · simp [ha,hb,labelReduce] at e
    · simp [ha,hb,labelReduce] at e
    · have he : (a:ZMod p)=(b:ZMod p) := by simpa only [ha,hb,labelReduce,Option.some.injEq] using e
      exact hp (((ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp he).trans
        ((slope_dvd_wheel Q slots hij ha hb).trans hm))

/-- Actual affine reading after reducing the original integer key. -/
theorem reading_reduce (p : ℕ) [Fact p.Prime] (Q u q : ℤ) (i : Option ℤ) :
    dot (affine (Q:ZMod p) (labelReduce p i)) ((u:ZMod p),(q:ZMod p)) =
      (originalForm Q u q i:ZMod p) := by
  cases i <;> simp [originalForm,labelReduce]

section Field
variable {K : Type*} [Field K]

theorem two_readings_determine (a b x y : V K) (h : det a b≠0)
    (hA : dot a x=dot a y) (hB : dot b x=dot b y) : x=y := by
  have agree (v : V K) : dot v x=dot v y := by
    rw [← coeff_recovery a b v x h, ← coeff_recovery a b v y h,hA,hB]
  apply Prod.ext
  · simpa [dot] using agree (1,0)
  · simpa [dot] using agree (0,1)
end Field

section Prime
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ℕ) [Fact p.Prime]

/-- The finite-field asymptotic is now stated at every prime off a literal
fixed integer wheel of the original slope family. -/
theorem density_at_prime (Q M : ℤ) (slots : (Fin 2 ⊕ ι) → Option ℤ)
    (hinj : Function.Injective slots)
    (hm : wheel Q slots∣M) (hp : ¬(p:ℤ)∣M) :
    let m : ℝ := Fintype.card ι
    let c : ℝ := χ (ZMod p)
    let g : ℝ := ((badResidues
      (mixed (Q:ZMod p) (fun i => labelReduce p (slots i)))).card:ℝ)/(p:ℝ)^4
    |g-(m+2+2*c)/(p:ℝ)| ≤ (5*m+6)/(p:ℝ)^2 := by
  obtain ⟨hp2,hQ,hslots⟩ := good_reduction p Q M slots hinj hm hp
  have htwo : (2:ZMod p)≠0 := by
    have h : ((2:ℤ):ZMod p)≠0 := fun e =>
      hp (((ZMod.intCast_zmod_eq_zero_iff_dvd (2:ℤ) p).mp e).trans
        ((two_dvd_wheel Q slots).trans hm))
    simpa only [Int.cast_ofNat] using h
  have hchar : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  simpa only [ZMod.card] using observed_density (Q:ZMod p)
    (fun i => labelReduce p (slots i)) hQ hslots hchar htwo

/-- For actual (possibly already congruent) readings, the original integer
forms are included exactly once by their distinct labels;
membership says precisely that one of them is divisible by p. -/
theorem bad_iff_original_divides (Q M u q : ℤ) (slots : (Fin 2 ⊕ ι) → Option ℤ)
    (hinj : Function.Injective slots)
    (hm : wheel Q slots∣M) (hp : ¬(p:ℤ)∣M) (z : Box (ZMod p))
    (hleft : norm z.1=(originalForm Q u q (slots (.inl 0)):ZMod p))
    (hright : norm z.2=(originalForm Q u q (slots (.inl 1)):ZMod p)) :
    z ∈ badResidues (mixed (Q:ZMod p) (fun i => labelReduce p (slots i))) ↔
      ∃ i, (p:ℤ)∣originalForm Q u q (slots i) := by
  obtain ⟨_,hQ,hslots⟩ := good_reduction p Q M slots hinj hm hp
  let a := affine (Q:ZMod p) (labelReduce p (slots (.inl 0)))
  let b := affine (Q:ZMod p) (labelReduce p (slots (.inl 1)))
  have h : det a b≠0 := affine_pairwise hQ
    (fun e => (by decide : (0:Fin 2)≠1) (Sum.inl.inj (hslots e)))
  have hre : keyResidue a b z = ((u:ZMod p),(q:ZMod p)) := by
    refine two_readings_determine a b _ _ h ?_ ?_
    · rw [(key_readback a b z h).1,hleft]
      exact (reading_reduce p Q u q _).symm
    · rw [(key_readback a b z h).2,hright]
      exact (reading_reduce p Q u q _).symm
  rw [membership_original (Q:ZMod p) (fun i => labelReduce p (slots i)) hQ hslots z]
  change (∃ i, dot (affine (Q:ZMod p) (labelReduce p (slots i))) (keyResidue a b z)=0) ↔ _
  simp only [hre,reading_reduce,ZMod.intCast_zmod_eq_zero_iff_dvd]
end Prime
end LinearA4FixedWheelResidues318
