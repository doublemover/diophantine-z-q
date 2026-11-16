module
public import ActualTwoDescentGaloisRootHalf318
public section
noncomputable section
namespace ActualTwoDescentGaloisEvenRootSigns318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentGaloisRootHalf318

lemma actual_galois_root_sign (σ : GalQ) (x : ℚ) (a : Qbar) (ha : a^2=algebraMap ℚ Qbar x) :
    σ a=a ∨ σ a= -a := by
  have hs := actual_galois_root_square σ x a ha
  have hm : (σ a-a)*(σ a+a)=0 := by linear_combination hs-ha
  rcases mul_eq_zero.mp hm with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · right; linear_combination h

/-- The actual product relation forces the four EVEN root-sign patterns when the original point is nonexceptional. -/
theorem actual_even_root_signs (σ : GalQ) (n x y : ℚ) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n)
    (han : a ≠ 0) (hbn : b ≠ 0) (hcn : c ≠ 0) (hp : a*b*c= -algebraMap ℚ Qbar y) :
    (σ a=a ∧ σ b=b ∧ σ c=c) ∨ (σ a=a ∧ σ b= -b ∧ σ c= -c) ∨
    (σ a= -a ∧ σ b=b ∧ σ c= -c) ∨ (σ a= -a ∧ σ b= -b ∧ σ c=c) := by
  have hprod : σ a*σ b*σ c=a*b*c := by rw [←map_mul,←map_mul,hp,map_neg,σ.commutes]
  have hne : a*b*c ≠ 0 := mul_ne_zero (mul_ne_zero han hbn) hcn
  have hb' : b^2=algebraMap ℚ Qbar (x-n) := by simpa only [map_sub] using hb
  have hc' : c^2=algebraMap ℚ Qbar (x+3*n) := by simpa only [map_add,map_mul,map_ofNat] using hc
  rcases actual_galois_root_sign σ x a ha with hA|hA <;>
    rcases actual_galois_root_sign σ (x-n) b hb' with hB|hB <;>
    rcases actual_galois_root_sign σ (x+3*n) c hc' with hC|hC
  all_goals first
    | exact Or.inl ⟨hA,hB,hC⟩
    | exact Or.inr (Or.inl ⟨hA,hB,hC⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨hA,hB,hC⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨hA,hB,hC⟩))
    | (exfalso; apply hne; rw [hA,hB,hC] at hprod; linear_combination -hprod/2)

end ActualTwoDescentGaloisEvenRootSigns318
