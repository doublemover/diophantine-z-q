module
public import ActualOriginalNonarchimedeanProduct318
public section
noncomputable section
namespace ActualAllPrimePrimitiveDensity318
open QuadricCRTAssembly318 ActualFullLocalDensityRecurrence318 ActualSingularResidueCount318
open ActualPrimitivePrimePower318 Filter
open scoped Topology
set_option maxHeartbeats 28000000

@[expose] def primitiveNormalized (κ : ℤ) (p n : ℕ) : ℚ :=
  (Nat.card (PrimitiveResidues κ (p^n) p):ℚ)/(p:ℚ)^(4*n)

/-- The SAME original singular scaling identity gives the primitive
normalization at EVERY prime, including2 and all odd bad places. -/
theorem actual_all_prime_primitive_difference (κ : ℤ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    primitiveNormalized κ p (e+2)=volume κ p (e+2)-volume κ p e/(p:ℚ)^3 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hh := actual_whole_quadric_split κ (p^e) p
  have he : p*(p^e*p)=p^(e+2) := by
    rw [show e+2=(e+1)+1 by omega,pow_succ p (e+1),pow_succ p e]
    ring
  rw [he] at hh
  have hN : (count κ p (e+2):ℚ)=
      (Nat.card (PrimitiveResidues κ (p^(e+2)) p):ℚ)+(p:ℚ)^5*(count κ p e:ℚ) := by
    have hcast := congrArg (fun n : ℕ => (n:ℚ)) hh
    simpa only [count,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,mul_comm] using hcast
  unfold primitiveNormalized volume
  rw [hN]
  have hden : (p:ℚ)^(4*(e+2))=(p:ℚ)^(4*e)*(p:ℚ)^8 := by
    rw [show 4*(e+2)=4*e+8 by omega,pow_add]
  rw [hden]
  field_simp [hp0]
  <;> ring

/-- Any produced limit of the ORIGINAL whole local residue counts
therefore yields the actual primitive local limit with correction1-p^-3.
The proof consumes the genuine singular fibers, not a Mobius heuristic. -/
theorem actual_primitive_limit_of_whole (κ : ℤ) (p : ℕ) (hp : p.Prime) (S : ℝ)
    (hS : Tendsto (fun n : ℕ => (volume κ p n:ℝ)) atTop (𝓝 S)) :
    Tendsto (fun n : ℕ => (primitiveNormalized κ p n:ℝ)) atTop (𝓝 (S*(1-1/(p:ℝ)^3))) := by
  have ha : Tendsto (fun n : ℕ => n+2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b,fun n hn => by omega⟩
  have hdiff : Tendsto (fun n : ℕ => (primitiveNormalized κ p (n+2):ℝ)) atTop
      (𝓝 (S-S/(p:ℝ)^3)) := by
    have he (n : ℕ) : (primitiveNormalized κ p (n+2):ℝ)=
        (volume κ p (n+2):ℝ)-(volume κ p n:ℝ)/(p:ℝ)^3 := by
      rw [actual_all_prime_primitive_difference κ p hp n]
      simp only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
    simp_rw [he]
    exact (hS.comp ha).sub (hS.div_const _)
  have hb : Tendsto (fun n : ℕ => n-2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b+2,fun n hn => by omega⟩
  have hh := hdiff.comp hb
  have hlim : S-S/(p:ℝ)^3=S*(1-1/(p:ℝ)^3) := by ring
  rw [hlim] at hh
  refine Tendsto.congr' ?_ hh
  exact eventually_atTop.2 ⟨2,fun n hn => by
    change (primitiveNormalized κ p (n-2+2):ℝ)=(primitiveNormalized κ p n:ℝ)
    rw [Nat.sub_add_cancel hn]⟩

end ActualAllPrimePrimitiveDensity318
