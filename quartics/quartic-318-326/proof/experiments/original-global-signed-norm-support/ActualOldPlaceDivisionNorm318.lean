module
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public section
noncomputable section

namespace ActualOldPlaceDivisionNorm318
open scoped BigOperators
variable {G A I : Type*} [Group G] [AddCommGroup A] [Fintype I]
variable (ρ : G →* AddMonoid.End A)

@[expose] def delta (g : G) (Q : A) : A := ρ g Q - Q

@[expose] def pointNorm (r : I → G) (Q : A) : A := ∑ i, ρ (r i) Q

/-- One actual evaluation of the bar transfer, with the left coset
permutation and h_{g,i}=r_{g i}^{−1} g r_i kept explicit. -/
@[expose] def transferAt (H : Subgroup G) (r : I → G) (e : Equiv.Perm I)
    (h : I → H) (b : H → A) : A := ∑ i, ρ (r (e i)) (b (h i))

theorem act_mul (g h : G) (Q : A) : ρ (g*h) Q = ρ g (ρ h Q) := by
  rw [map_mul] <;> rfl

theorem delta_add (g : G) (P Q : A) :
    delta ρ g (P+Q) = delta ρ g P + delta ρ g Q := by
  simp only [delta,map_add]
  abel

theorem delta_sub (g : G) (P Q : A) :
    delta ρ g (P-Q) = delta ρ g P - delta ρ g Q := by
  simp only [delta,map_sub]
  abel

theorem delta_nsmul (g : G) (L : ℕ) (P : A) :
    delta ρ g (L • P) = L • delta ρ g P := by
  simp only [delta,map_nsmul,nsmul_sub]

theorem delta_zsmul (g : G) (m : ℤ) (P : A) :
    delta ρ g (m • P) = m • delta ρ g P := by
  simp only [delta,map_zsmul,zsmul_sub]

theorem pointNorm_nsmul (r : I → G) (a : ℕ) (Q : A) :
    pointNorm ρ r (a • Q) = a • pointNorm ρ r Q := by
  simp only [pointNorm,map_nsmul,Finset.smul_sum]

private theorem nat_zsmul_comm (a : ℕ) (m : ℤ) (x : A) :
    a • (m • x) = m • (a • x) := by
  calc
    _ = (a:ℤ) • (m • x) := (Nat.cast_smul_eq_nsmul ℤ a _).symm
    _ = m • ((a:ℤ) • x) := by rw [smul_smul,smul_smul,mul_comm (a:ℤ) m]
    _ = _ := by rw [Nat.cast_smul_eq_nsmul ℤ]

/-- Strict finite evaluation of Kummer corestriction on the actual division
sum with the same coset indices. This uses no division by the index. -/
theorem transfer_division_at (H : Subgroup G) (r : I → G) (g : G)
    (e : Equiv.Perm I) (h : I → H)
    (tile : ∀ i, r (e i) * (h i : G) = g * r i) (Q : A) :
    transferAt ρ H r e h (fun u => delta ρ (u:G) Q) =
      delta ρ g (pointNorm ρ r Q) := by
  have hreindex : ∑ i, ρ (r (e i)) Q = ∑ i, ρ (r i) Q :=
    Equiv.sum_comp e (fun i => ρ (r i) Q)
  calc
    _ = ∑ i, (ρ g (ρ (r i) Q) - ρ (r (e i)) Q) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [delta,map_sub,←act_mul,tile i]
    _ = _ := by
      rw [Finset.sum_sub_distrib,hreindex]
      simp only [delta,pointNorm,map_sum]

/-- The explicit old-place H22 boundary with the SAME q and the SAME
chosen lower division W. m may have either sign. The upper division
Q, H22 witness q, and the lower division W are all retained. -/
theorem signed_norm_h22_at (H : Subgroup G) (r : I → G) (g : G)
    (e : Equiv.Perm I) (h : I → H)
    (tile : ∀ i, r (e i) * (h i : G) = g * r i)
    (a : ℕ) (P₊ P₀ Q W q : A)
    (hQ : a • Q = P₊) (hW : a • W = P₀) (hq : a • q = 0)
    (m : ℤ) (hnorm : pointNorm ρ r P₊ = m • P₀)
    (b : H → A)
    (hb : ∀ u : H, b u = delta ρ (u:G) Q + delta ρ (u:G) q)
    (L : ℕ) :
    let T := pointNorm ρ r (Q+q) - m • W
    a • T = 0 ∧
      L • transferAt ρ H r e h b - L • (m • delta ρ g W) =
        delta ρ g (L • T) := by
  dsimp only
  constructor
  · rw [nsmul_sub,←pointNorm_nsmul,nsmul_add,hQ,hq,add_zero,
      nat_zsmul_comm,hW,hnorm,sub_self]
  · have htr : transferAt ρ H r e h b = delta ρ g (pointNorm ρ r (Q+q)) := by
      rw [←transfer_division_at ρ H r g e h tile (Q+q)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hb,delta_add]
    rw [htr,←nsmul_sub,←delta_zsmul,←delta_sub,delta_nsmul]

/-- On the SAME local cocycle that has this division representative,
a change of section adds its exact finite correction; no new division
point is selected. This is the local Kummer form of the H21 sign. -/
theorem section_norm_difference (r r' : I → G) (j : I → G)
    (hr : ∀ i, r' i = r i * j i) (Q : A) :
    pointNorm ρ r' Q - pointNorm ρ r Q =
      ∑ i, ρ (r i) (delta ρ (j i) Q) := by
  rw [pointNorm,pointNorm,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i,act_mul,delta,map_sub]

/-- Combine independently adapted local orbits using the ACTUAL
coefficient pushes. The intertwining condition keeps the θ(t_i)
weights in the coefficient module, not extra scalars on elliptic points. -/
theorem combine_orbits {M : Type*} [AddCommGroup M]
    (push : I → A →+ M) (g : I → G) (gM : M →+ M)
    (hc : ∀ i x, push i (ρ (g i) x) = gM (push i x))
    (z w T : I → A) (h : ∀ i, z i - w i = delta ρ (g i) (T i)) :
    (∑ i, push i (z i)) - (∑ i, push i (w i)) =
      gM (∑ i, push i (T i)) - ∑ i, push i (T i) := by
  rw [map_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←map_sub,h i,delta,map_sub,hc]

end ActualOldPlaceDivisionNorm318

#print axioms ActualOldPlaceDivisionNorm318.signed_norm_h22_at
#print axioms ActualOldPlaceDivisionNorm318.combine_orbits
