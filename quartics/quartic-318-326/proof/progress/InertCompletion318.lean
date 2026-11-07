module
public import DiscreteCompletion318
public import InertPlace318
public section
namespace InertCompletion318
open ConcreteG8Domain
open DiscreteCompletion318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [hp:Fact p.Prime] (nonsquare:¬∃x:ZMod p,x^2=2)

 theorem prime_gt_one : (1:ℝ)<p := by exact_mod_cast hp.out.one_lt
@[expose] abbrev Field := Completion (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare)
@[expose] def embedding : K →+* Field p nonsquare :=
  embed (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare)

instance : NontriviallyNormedField (Field p nonsquare) :=
  nontriviallyNormed (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare) (p:K)
    (InertPlace318.place_prime p nonsquare)

 theorem embedding_injective : Function.Injective (embedding p nonsquare) :=
  (embedding p nonsquare).injective

 theorem norm_embedding (x:K) : ‖embedding p nonsquare x‖=magnitude (p:ℝ) (InertPlace318.place p nonsquare x) :=
  norm_embed (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare) x

 theorem norm_embedding_value (x:K) (a:ℤ) (hx:InertPlace318.place p nonsquare x=a) :
    ‖embedding p nonsquare x‖=(p:ℝ)^(-a) :=
  norm_embed_value (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare) x a hx

 theorem rational_norm (q:ℚ) : ‖embedding p nonsquare (pair q 0)‖=‖(q:ℚ_[p])‖ := by
  by_cases hq:q=0
  · simp [hq,pair]
  · rw [norm_embedding,InertPlace318.place_rational,ConcretePadic318.rational_value p q hq,magnitude_coe]
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),Padic.valuation_ratCast]

 theorem norm_ratCast (q:ℚ) : ‖(q:Field p nonsquare)‖=‖(q:ℚ_[p])‖ := by
  have hq:pair q 0=(q:K) := by ext <;> norm_num [pair]
  simpa only [hq,map_ratCast] using rational_norm p nonsquare q

 theorem norm_prime : ‖embedding p nonsquare (p:K)‖=(p:ℝ)⁻¹ := by
  rw [norm_embedding_value p nonsquare (p:K) 1 (InertPlace318.place_prime p nonsquare)]
  simp

 theorem norm_pair (a b:ℚ) :
    ‖embedding p nonsquare (pair a b)‖=max ‖(a:ℚ_[p])‖ ‖(b:ℚ_[p])‖ := by
  rw [norm_embedding,InertPlace318.place_pair,magnitude_min _ (prime_gt_one p).le]
  rw [←InertPlace318.place_rational p nonsquare a,←InertPlace318.place_rational p nonsquare b,
    ←norm_embedding,←norm_embedding,rational_norm,rational_norm]

 theorem norm_bound_iff (x:K) (a:ℤ) :
    ‖embedding p nonsquare x‖≤(p:ℝ)^(-a) ↔ (a:WithTop ℤ)≤InertPlace318.place p nonsquare x :=
  norm_embed_le_iff (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare) x a

 theorem norm_lt_one_iff (x:K) :
    ‖embedding p nonsquare x‖<1 ↔ (0:WithTop ℤ)<InertPlace318.place p nonsquare x :=
  norm_embed_lt_one_iff (p:ℝ) (prime_gt_one p) (InertPlace318.place p nonsquare) x

 theorem sqrt_two : (embedding p nonsquare i)^2=2 := by
  rw [←map_pow]
  have hi:i^2=(2:K) := by ext <;> norm_num [i,pair,pow_succ]
  rw [hi,map_ofNat]

 example : CompleteSpace (Field p nonsquare) := inferInstance
 example : CharZero (Field p nonsquare) := inferInstance
 example : IsUltrametricDist (Field p nonsquare) := inferInstance

end
end InertCompletion318
#print axioms InertCompletion318.rational_norm
#print axioms InertCompletion318.norm_pair
#print axioms InertCompletion318.sqrt_two
