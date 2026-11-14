module
public import ActualLocalPrimitiveNormalization318
public section
noncomputable section
namespace ActualOriginalLocalFactorConsumer318
open scoped BigOperators
open QuadricCRTAssembly318 PrimitiveSieveCRT318 OriginalSieveCRTProduct318
open ActualLocalVolumeClosedForm318 ActualLocalPrimitiveNormalization318
set_option maxHeartbeats 24000000
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

lemma original_primitive_ratio (p : ℕ) (hp : p.Prime) :
    (((p^4-1:ℕ):ℚ)/(p:ℚ)^4)=localFactor p*(1-ratio p) := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hp4 : 1≤p^4 := one_le_pow₀ (show 1≤p by omega)
  have hd : 1-ratio p≠0 := ne_of_gt (sub_pos.mpr (ratio_lt_one p hp))
  rw [Nat.cast_sub hp4,Nat.cast_pow,Nat.cast_one,localFactor,div_mul_cancel₀ _ hd]
  field_simp [hp0]
  <;> ring

/-- The ORIGINAL single-modulus primitive CRT count consumes these
same unrestricted local factors and their genuine singular correction.
The product is finite; no Euler product convergence is asserted here. -/
theorem actual_primitive_crt_volume (p : ι → ℕ) (hp : ∀i,(p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hp2 : ∀i,p i≠2) (hκ : ∀i,¬(p i:ℤ)∣κ) :
    (Nat.card (Primitive p hp hd κ):ℚ)/(FixedSquarefreeCRT318.modulus p:ℚ)^4=
      (∏i,localFactor (p i))*(∏i,1-ratio (p i)) := by
  rw [primitive_card p hp hd κ hp2 hκ]
  simp only [FixedSquarefreeCRT318.modulus,Nat.cast_prod,Finset.prod_pow]
  rw [←Finset.prod_div_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact original_primitive_ratio (p i) (hp i)

/-- The actual original local bad-event density is conditional on the
primitive locus. Relative to the unrestricted local density, the exact
additional factor is 1-p^-3; no change of the original sieve event. -/
theorem actual_bad_volume_fraction (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (κ : ℤ) (hκ : ¬(p:ℤ)∣κ) (γ : J → ℤ) (j₀ : J) :
    ((Nat.card (badSet (κ:ZMod p) (fun j => (γ j:ZMod p))):ℚ)/(p:ℚ)^4)/localFactor p=
      densityAt p hp κ γ j₀*(1-ratio p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hl := local_density p hp2 κ hκ γ j₀
  change (Nat.card (badSet (κ:ZMod p) (fun j => (γ j:ZMod p))):ℚ)/((p^4-1:ℕ):ℚ)=
    densityAt p hp κ γ j₀ at hl
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h2 : (1:ℚ)<(p:ℚ)^2 := by nlinarith [sq_nonneg ((p:ℚ)-1)]
  have h4 : (1:ℚ)<(p:ℚ)^4 := by nlinarith [sq_nonneg ((p:ℚ)^2-1)]
  have hN : ((p^4-1:ℕ):ℚ)≠0 := by
    rw [Nat.cast_sub (one_le_pow₀ (show 1≤p by omega)),Nat.cast_pow,Nat.cast_one]
    exact ne_of_gt (sub_pos.mpr h4)
  have hs : localFactor p≠0 := ne_of_gt (lt_trans (by norm_num) (actual_factor_gt_one p hp))
  rw [←hl]
  have hr := original_primitive_ratio p hp
  apply (div_eq_iff hs).mpr
  calc
    _ = ((Nat.card (badSet (κ:ZMod p) (fun j => (γ j:ZMod p))):ℚ)/((p^4-1:ℕ):ℚ))*
        (((p^4-1:ℕ):ℚ)/(p:ℚ)^4) := by field_simp [hN,hp0]
    _ = _ := by rw [hr];ring

end ActualOriginalLocalFactorConsumer318
