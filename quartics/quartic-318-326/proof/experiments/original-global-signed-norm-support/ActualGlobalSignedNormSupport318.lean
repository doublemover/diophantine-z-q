module
public import ActualOldPlaceDivisionNorm318
public import ActualSupportedPrimitiveRetention318
import Mathlib.Tactic.Abel
public section

namespace ActualGlobalSignedNormSupport318
open ActualOldPlaceDivisionNorm318 ActualSupportedPrimitiveRetention318
open scoped BigOperators

variable {G Γ M A I : Type*} [Group G] [Group Γ]
variable [AddCommGroup M] [AddCommGroup A] [Fintype I]

/-- The signed empty-derivative H21 row at the actual common support.
The coefficient realization iT is only the a-torsion module; the
geometric action on arbitrary division points is NOT assumed supported.
The marked point norm and both original cocycle comparisons are supplied.
The resulting supported boundary is the same explicit norm primitive. -/
theorem supported_signed_norm
    (π : G →* Γ) (hπ : Function.Surjective π)
    (ρ : G →* AddMonoid.End A) (ρS : Γ →* AddMonoid.End M)
    (iT : M →+ A) (iTinj : Function.Injective iT)
    (compat : ∀ g x, ρ g (iT x) = iT (ρS (π g) x))
    (a L : ℕ) (m : ℤ)
    (Mkill : ∀ x : M, a • x = 0)
    (ont : ∀ x : A, a • x = 0 → ∃ y : M, iT y = x)
    (H : Subgroup G) (r : I → G) (e : G → Equiv.Perm I) (h : G → I → H)
    (tile : ∀ g i, r (e g i) * (h g i : G) = g * r i)
    (P₊ P₀ Q W : A) (hQ : a • Q = P₊) (hW : a • W = P₀)
    (hnorm : pointNorm ρ r P₊ = m • P₀)
    (cPlus c₀ ν : M) (b : H → A) (z b₀ : Γ → M)
    (hb : ∀ x : H, b x = L • delta ρ (x:G) Q + delta ρ (x:G) (iT cPlus))
    (hz : ∀ g, iT (z (π g)) = transferAt ρ H r (e g) (h g) b + delta ρ g (iT ν))
    (hb₀ : ∀ g, iT (b₀ (π g)) = delta ρ g W + delta ρ g (iT c₀)) :
    let w := L • (pointNorm ρ r Q - m • W) + pointNorm ρ r (iT cPlus) -
      iT (L • (m • c₀)) + iT ν
    ∃ t : M, iT t = w ∧ ∀ g, z g - L • (m • b₀ g) = ρS g t - t := by
  dsimp only
  have hD (g : G) :
      a • (pointNorm ρ r Q - m • W) = 0 ∧
        L • transferAt ρ H r (e g) (h g) (fun x => delta ρ (x:G) Q) -
          L • (m • delta ρ g W) = delta ρ g (L • (pointNorm ρ r Q - m • W)) := by
    have hh := signed_norm_h22_at ρ H r g (e g) (h g) (tile g)
      a P₊ P₀ Q W 0 hQ hW (nsmul_zero a) m hnorm (fun x => delta ρ (x:G) Q)
      (by intro x; simp only [delta,map_zero,sub_zero,add_zero]) L
    simpa only [add_zero] using hh
  have kill_i (x : M) : a • iT x = 0 := by rw [←map_nsmul,Mkill,map_zero]
  have kill_L : a • (L • (pointNorm ρ r Q - m • W)) = 0 := by
    rw [←mul_nsmul,Nat.mul_comm a L,mul_nsmul,(hD (1:G)).1,nsmul_zero]
  have kill_N : a • pointNorm ρ r (iT cPlus) = 0 := by
    rw [←pointNorm_nsmul,kill_i]
    simp only [pointNorm,map_zero,Finset.sum_const_zero]
  have kill : a • (L • (pointNorm ρ r Q - m • W) + pointNorm ρ r (iT cPlus) -
      iT (L • (m • c₀)) + iT ν) = 0 := by
    rw [nsmul_add,nsmul_sub,nsmul_add]
    simp only [kill_L,kill_N,kill_i,add_zero,sub_zero]
  obtain ⟨t,ht⟩ := ont _ kill
  refine ⟨t,ht,supported_boundary π hπ ρS z (fun g => L • (m • b₀ g)) t ?_⟩
  intro g
  apply iTinj
  have hb' : b = fun x : H => delta ρ (x:G) (L • Q + iT cPlus) := by
    funext x
    rw [hb,delta_add,delta_nsmul]
  have hN : pointNorm ρ r (L • Q + iT cPlus) =
      L • pointNorm ρ r Q + pointNorm ρ r (iT cPlus) := by
    rw [←pointNorm_nsmul]
    simp only [pointNorm,map_add,Finset.sum_add_distrib]
  have htr : transferAt ρ H r (e g) (h g) b =
      L • transferAt ρ H r (e g) (h g) (fun x => delta ρ (x:G) Q) +
        delta ρ g (pointNorm ρ r (iT cPlus)) := by
    rw [hb',transfer_division_at ρ H r g (e g) (h g) (tile g),hN,delta_add,delta_nsmul,
      ←transfer_division_at ρ H r g (e g) (h g) (tile g) Q]
  rw [map_sub,map_nsmul,map_zsmul,hz,hb₀,map_sub,←compat,ht,htr]
  change _ = delta ρ g (L • (pointNorm ρ r Q - m • W) + pointNorm ρ r (iT cPlus) -
    iT (L • (m • c₀)) + iT ν)
  rw [delta_add,delta_sub,delta_add,←(hD g).2]
  rw [map_nsmul,map_zsmul,delta_nsmul,delta_zsmul,zsmul_add,nsmul_add]
  abel

end ActualGlobalSignedNormSupport318

#print axioms ActualGlobalSignedNormSupport318.supported_signed_norm
