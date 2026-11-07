module
public import LocalMahlerHeight
public section
noncomputable section
open NumberField Height Ideal
namespace FiniteHeightEquiv
set_option maxHeartbeats 0
variable {F G : Type*} [Field F] [Field G] [NumberField F] [NumberField G]

lemma absNorm_map_equiv (e : 𝓞 F ≃+* 𝓞 G) (I : Ideal (𝓞 F)) :
    (I.map (e : 𝓞 F →+* 𝓞 G)).absNorm=I.absNorm := by
  simp only [Ideal.absNorm_apply,Submodule.cardQuot]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ e rfl).toEquiv).symm

lemma finite_max_support (x : F) :
    Function.HasFiniteMulSupport (fun v : FinitePlace F => max (v x) 1) := by
  by_cases hx : x=0
  · subst x; simpa [Function.HasFiniteMulSupport,Function.mulSupport]
  · apply (FinitePlace.hasFiniteMulSupport hx).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv ⊢
    contrapose! hv
    simp [hv]

lemma finite_part_of_normalized_denominator (x : F) (n : ℕ) (hn : n≠0)
    (a : 𝓞 F) (ha : (n:F)*x=(a:F))
    (hN : (Ideal.span {(n:𝓞 F),a}).absNorm=n^(Module.finrank ℚ F-1)) :
    (∏ᶠ v : FinitePlace F, max (v x) 1)=(n:ℝ) := by
  have hnF : (n:F)≠0 := by exact_mod_cast hn
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
  have hpair : (![ (n:𝓞 F),a] : Fin 2 → 𝓞 F) ≠ 0 := by
    intro h; have h0 : (n:𝓞 F)=0 := by simpa using congrFun h 0
    exact hn (by exact_mod_cast h0)
  have hp := NumberField.absNorm_mul_finprod_finitePlace_eq_one hpair
  have hrange : Set.range (![ (n:𝓞 F),a] : Fin 2 → 𝓞 F)={(n:𝓞 F),a} := by
    ext z; simp [Set.mem_range,Fin.exists_fin_two,or_comm]
  rw [hrange,hN] at hp
  have hv (v : FinitePlace F) :
      (⨆ i : Fin 2, v ((![ (n:𝓞 F),a] i : 𝓞 F):F)) = v (n:F)*max (v x) 1 := by
    rw [RationalAbsoluteHeight.iSup_pair]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,←ha,map_mul]
    have hc : ((n:𝓞 F):F)=(n:F) := by simp
    rw [hc,mul_max_of_nonneg _ _ (apply_nonneg v (n:F)),mul_one,max_comm]
  simp_rw [hv] at hp
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hnF) (finite_max_support x),
    FinitePlace.prod_eq_inv_abs_norm hnF,Algebra.norm_natCast] at hp
  have hnorm : ((|(n:ℚ)^Module.finrank ℚ F|⁻¹:ℚ):ℝ)=((n:ℝ)^Module.finrank ℚ F)⁻¹ := by
    simp [abs_of_nonneg (by positivity : (0:ℚ)≤(n:ℚ)^Module.finrank ℚ F)]
  rw [hnorm] at hp
  have hd : 0<Module.finrank ℚ F := Module.finrank_pos
  have hpow : (n:ℝ)^Module.finrank ℚ F = (n:ℝ)^(Module.finrank ℚ F-1)*(n:ℝ) := by
    rw [←pow_succ,Nat.sub_add_cancel hd]
  push_cast at hp
  rw [hpow] at hp
  field_simp at hp
  nlinarith [pow_pos (show (0:ℝ)<n by exact_mod_cast Nat.pos_of_ne_zero hn) (Module.finrank ℚ F-1)]

lemma finite_part_equiv (e : F ≃+* G) (x : F) :
    (∏ᶠ v : FinitePlace G, max (v (e x)) 1) =
      ∏ᶠ v : FinitePlace F, max (v x) 1 := by
  obtain ⟨n,hn,a,ha,hN⟩ :=
    NumberField.exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  rw [finite_part_of_normalized_denominator x n hn a ha hN]
  let eO := RingOfIntegers.mapRingEquiv e
  apply finite_part_of_normalized_denominator (e x) n hn (eO a)
  · have h := congrArg e ha
    simpa [eO,RingOfIntegers.mapRingEquiv_apply] using h
  · have hd : Module.finrank ℚ F=Module.finrank ℚ G := e.toRatAlgEquiv.toLinearEquiv.finrank_eq
    rw [←hd,←hN]
    have hm : Ideal.span {(n:𝓞 G),eO a} =
        (Ideal.span {(n:𝓞 F),a}).map (eO : 𝓞 F →+* 𝓞 G) := by
      rw [Ideal.map_span]
      simp
    rw [hm,absNorm_map_equiv]

#print axioms absNorm_map_equiv
#print axioms finite_max_support
#print axioms finite_part_of_normalized_denominator
#print axioms finite_part_equiv
end FiniteHeightEquiv
