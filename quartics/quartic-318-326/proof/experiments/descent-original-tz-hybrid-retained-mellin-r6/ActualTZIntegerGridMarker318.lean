module
public import ActualTZSignedGridPushforward318
import all ActualTZSignedGridPushforward318
import all ActualTZSignedAxisSupport318
public section
noncomputable section
namespace ActualTZIntegerGridMarker318
open scoped BigOperators
open ActualTZSignedGridPushforward318 ActualTZSignedAxisSupport318

variable {n p : ℕ} [NeZero p] [Fact p.Prime]

@[expose] def reduced (D : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin n) (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p)) D

theorem reduced_ne (D : MvPolynomial (Fin n) ℤ) (u : Fin n→₀ℕ)
    (hu : ¬(p:ℤ)∣D.coeff u) : reduced (p:=p) D≠0 := by
  intro H
  apply hu
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (D.coeff u) p).1
  change (Int.castRingHom (ZMod p)) (D.coeff u)=0
  rw [←MvPolynomial.coeff_map]
  change (reduced (p:=p) D).coeff u=0
  simp only [H,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]

theorem reduced_degree (D : MvPolynomial (Fin n) ℤ) :
    (reduced (p:=p) D).totalDegree≤D.totalDegree := by
  have h : (MvPolynomial.map (Int.castRingHom (ZMod p)) D).support⊆D.support :=
    MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) D
  exact MvPolynomial.totalDegree_le_of_support_subset h

/-- Exact signed polynomial condition. No change of offset,
orientation, or integer wrap constant in the reduction. -/
theorem residue_root (L : Fin n→ℕ) (s : Fin n→ℤ) (t : Grid L)
    (D : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval (residue (p:=p) L s t) (reduced D)=0 ↔
      (p:ℤ)∣MvPolynomial.eval (fun i=>s i+(t i).val) D := by
  have H := MvPolynomial.map_eval (Int.castRingHom (ZMod p)) (fun i=>s i+(t i).val) D
  change ((_ : ℤ):ZMod p)=MvPolynomial.eval (residue L s t) (reduced D) at H
  rw [←H]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ p

/-- Exposed arithmetic marginal for every original signed grid
whose actual marker coefficient survives. d=2 on the literal rows. -/
theorem integer_probability_le (L : Fin n→ℕ) (s : Fin n→ℤ) (M d : ℕ)
    (hM : 0<M) (hL : ∀ i,M≤L i)
    (D : MvPolynomial (Fin n) ℤ) (hd : D.totalDegree≤d)
    (u : Fin n→₀ℕ) (hu : ¬(p:ℤ)∣D.coeff u) :
    (∑ t : Grid L,if (p:ℤ)∣MvPolynomial.eval (fun i=>s i+(t i).val) D then
        (∏ i : Fin n,1/(L i:ℚ≥0)) else 0)≤
      (2:ℚ≥0)^n*((n:ℚ≥0)*((d:ℚ≥0)/((min M p:ℕ):ℚ≥0))) := by
  have H := probability_le (p:=p) L s M d hM hL (reduced D) (reduced_ne D u hu)
    ((reduced_degree (p:=p) D).trans hd)
  refine le_trans (le_of_eq ?_) H
  unfold probability
  apply Finset.sum_congr rfl
  intro t _
  have ht := residue_root (p:=p) L s t D
  by_cases h : (p:ℤ)∣MvPolynomial.eval (fun i=>s i+(t i).val) D
  · rw [if_pos h,if_pos (ht.mpr h)]
  · rw [if_neg h,if_neg (fun h' => h (ht.mp h'))]

end ActualTZIntegerGridMarker318
