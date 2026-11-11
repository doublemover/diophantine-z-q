module
public import ActualFiniteGaussianPositionTail318
public section
noncomputable section
namespace ActualSamePositionDivisors318
open scoped BigOperators
open IntegerResidueBoxCount318 ActualSquareDivisibleValues318
set_option maxHeartbeats 12000000

/-- Both ORIGINAL adjacent norms at one Gaussian position. At odd primes
this is exactly the coprime pair a and b²+1, derived here rather than
assumed as a box-sieve hypothesis. -/
theorem actual_adjacent_iff (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (a b : ℤ) :
    ((p:ℤ)∣(a+1)^2+b^2 ∧ (p:ℤ)∣(a-1)^2+b^2) ↔
      ((p:ℤ)∣a ∧ (p:ℤ)∣b^2+1) := by
  have h4 : ¬(p:ℤ)∣4 := by
    intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (4:ℤ) p).mpr hd
    have h2 := GoodReductionResidue318.two_residue_ne p hp2
    have hn : (4:ZMod p)≠0 := by
      have he : (4:ZMod p)=2*2 := by norm_num
      rw [he]
      exact mul_ne_zero h2 h2
    exact hn (by simpa only [Int.cast_ofNat] using hh)
  constructor
  · rintro ⟨hp,hm⟩
    have hd : (p:ℤ)∣4*a := by
      convert dvd_sub hp hm using 1 <;> ring
    have ha := (LiteralAdjacentNormSlice318.prime_cancel p 4 a h4).mp hd
    have hz : (p:ℤ)∣a*(a+2) := dvd_mul_of_dvd_left ha _
    have hb : (p:ℤ)∣b^2+1 := by
      convert dvd_sub hp hz using 1 <;> ring
    exact ⟨ha,hb⟩
  · rintro ⟨ha,hb⟩
    constructor
    · convert dvd_add (dvd_mul_of_dvd_left ha (a+2)) hb using 1 <;> ring
    · convert dvd_add (dvd_mul_of_dvd_left ha (a-2)) hb using 1 <;> ring

@[expose] def Triple (B : ℕ) := Interval B×Interval B×Interval B
@[expose] def Source (B Y : ℕ) := {v : Triple B // ∃ p : ℕ,
  p.Prime ∧ Y<p ∧ (p:ℤ)∣(v.1.1+1)^2+v.2.1.1^2 ∧
    (p:ℤ)∣(v.1.1-1)^2+v.2.1.1^2}
@[expose] def normValue (b : ℤ) : ℕ := (b^2+1).natAbs
lemma normValue_pos (b : ℤ) : 0<normValue b := by
  apply Int.natAbs_pos.mpr
  have hh := sq_nonneg b
  omega
lemma normValue_cast (b : ℤ) : (normValue b:ℤ)=b^2+1 := by
  rw [normValue,Int.natCast_natAbs,abs_of_pos (by nlinarith [sq_nonneg b])]
@[expose] def primes (b : ℤ) (Y : ℕ) : Finset ℕ :=
  (normValue b).divisors.filter (fun p => p.Prime ∧ Y<p)
lemma mem_primes (b : ℤ) (Y p : ℕ) (hp : p.Prime) (hY : Y<p)
    (hd : (p:ℤ)∣b^2+1) : p∈primes b Y := by
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨?_,(normValue_pos b).ne'⟩,hp,hY⟩
  simpa only [Int.natAbs_natCast,normValue] using Int.natAbs_dvd_natAbs.mpr hd

@[expose] def Target (B Y : ℕ) :=
  (Interval B×Interval B) ⊕
    (Σ b : Interval B, Σ p : ↥(primes b.1 Y), Values B p.1×Interval B)
@[expose] def forget (B Y : ℕ) : Target B Y → Triple B :=
  Sum.elim (fun v => (⟨0,Finset.mem_Icc.mpr (by constructor <;> omega)⟩,v.1,v.2))
    (fun v => (v.2.2.1.1,v.1,v.2.2.2))
lemma actual_source_cover (B Y : ℕ) (hY : 2≤Y) (v : Source B Y) :
    ∃ z : Target B Y,forget B Y z=v.1 := by
  by_cases ha : v.1.1.1=0
  · refine ⟨Sum.inl (v.1.2.1,v.1.2.2),?_⟩
    apply Prod.ext
    · exact Subtype.ext ha.symm
    · rfl
  obtain ⟨p,hp,hYp,hplus,hminus⟩ := v.2
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by omega
  obtain ⟨hpa,hpb⟩ := (actual_adjacent_iff p hp2 v.1.1.1 v.1.2.1.1).mp ⟨hplus,hminus⟩
  exact ⟨Sum.inr ⟨v.1.2.1,⟨p,mem_primes _ Y p hp hYp hpb⟩,
    ⟨v.1.1,ha,hpa⟩,v.1.2.2⟩,rfl⟩
@[expose] def sourceChoice (B Y : ℕ) (hY : 2≤Y) : Source B Y → Target B Y :=
  fun v => (actual_source_cover B Y hY v).choose
lemma choice_injective (B Y : ℕ) (hY : 2≤Y) : Function.Injective (sourceChoice B Y hY) := by
  intro v w he
  apply Subtype.ext
  have hh := congrArg (forget B Y) he
  simpa only [sourceChoice,(actual_source_cover B Y hY v).choose_spec,
    (actual_source_cover B Y hY w).choose_spec] using hh

end ActualSamePositionDivisors318
