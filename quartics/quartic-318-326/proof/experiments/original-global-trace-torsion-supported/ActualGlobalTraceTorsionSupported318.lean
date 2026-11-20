module
public import ActualOldPlaceDivisionNorm318
public import ActualSupportedPrimitiveRetention318
public section

namespace ActualGlobalTraceTorsionSupported318
open ActualOldPlaceDivisionNorm318 ActualSupportedPrimitiveRetention318
open scoped BigOperators

variable {G Γ A M I : Type*} [Group G] [Group Γ]
variable [AddCommGroup A] [AddCommGroup M] [Fintype I]

/-- Direct annihilator of the SAME original supported finite H20 row.
The CCL signed point equality and torsion of the SAME marked P enter.
No lower Kummer cocycle, lower division, or ordinary Kummer comparison
map is needed. Only the finite k-torsion action is required supported. -/
theorem supported_mul_trace_torsion
    (π : G →* Γ) (onto : Function.Surjective π)
    (ρ : G →* AddMonoid.End A) (ρS : Γ →* AddMonoid.End M)
    (iT : M →+ A) (inj : Function.Injective iT)
    (compat : ∀ g x, ρ g (iT x) = iT (ρS (π g) x))
    (k L a : ℕ) (m : ℤ)
    (killM : ∀ x : M, k • x = 0)
    (tor : ∀ x : A, k • x = 0 → ∃ y : M, iT y = x)
    (H : Subgroup G) (r : I → G) (e : G → Equiv.Perm I) (h : G → I → H)
    (tile : ∀ g i, r (e g i) * (h g i : G) = g * r i)
    (P₊ P Q : A) (hQ : k • Q = P₊)
    (hnorm : pointNorm ρ r P₊ = m • P) (haP : a • P = 0)
    (cPlus ν : M) (b : H → A) (z : Γ → M)
    (hb : ∀ x : H, b x = L • delta ρ (x:G) Q + delta ρ (x:G) (iT cPlus))
    (hz : ∀ g, iT (z (π g)) = transferAt ρ H r (e g) (h g) b + delta ρ g (iT ν)) :
    let U := L • pointNorm ρ r Q + pointNorm ρ r (iT cPlus) + iT ν
    ∃ v : M, iT v = a • U ∧ ∀ g, a • z g = ρS g v - v := by
  dsimp only
  have hP : a • (m • P) = 0 := by
    calc
      _ = (a:ℤ) • (m • P) := (Nat.cast_smul_eq_nsmul ℤ a _).symm
      _ = m • ((a:ℤ) • P) := by rw [smul_smul,smul_smul,mul_comm (a:ℤ) m]
      _ = 0 := by rw [Nat.cast_smul_eq_nsmul ℤ,haP,smul_zero]
  have hNorm : k • pointNorm ρ r Q = m • P := by rw [←pointNorm_nsmul,hQ,hnorm]
  have hKill (x : M) : k • iT x = 0 := by rw [←map_nsmul,killM,map_zero]
  have hNormT : k • pointNorm ρ r (iT cPlus) = 0 := by
    rw [←pointNorm_nsmul,hKill]
    simp only [pointNorm,map_zero,Finset.sum_const_zero]
  let U := L • pointNorm ρ r Q + pointNorm ρ r (iT cPlus) + iT ν
  have hu : k • U = L • (m • P) := by
    dsimp only [U]
    rw [nsmul_add,nsmul_add,←mul_nsmul,Nat.mul_comm k L,mul_nsmul,
      hNorm,hNormT,hKill,add_zero,add_zero]
  have ht : k • (a • U) = 0 := by
    rw [←mul_nsmul,Nat.mul_comm k a,mul_nsmul,hu,←mul_nsmul,Nat.mul_comm a L,
      mul_nsmul,hP,nsmul_zero]
  obtain ⟨v,hv⟩ := tor _ ht
  have hb' : b = fun x : H => delta ρ (x:G) (L • Q + iT cPlus) := by
    funext x
    rw [hb,delta_add,delta_nsmul]
  have hN : pointNorm ρ r (L • Q + iT cPlus) =
      L • pointNorm ρ r Q + pointNorm ρ r (iT cPlus) := by
    rw [←pointNorm_nsmul]
    simp only [pointNorm,map_add,Finset.sum_add_distrib]
  have hz' (g : G) : iT (z (π g)) = delta ρ g U := by
    rw [hz,hb',transfer_division_at ρ H r g (e g) (h g) (tile g),hN,←delta_add]
  have hAbs : ∀ g : G, a • z (π g) - (0:M) = ρS (π g) v - v := by
    intro g
    apply inj
    rw [sub_zero,map_nsmul,hz',←delta_nsmul,map_sub,←compat,hv] <;> rfl
  have hS := supported_boundary π onto ρS (fun g => a • z g) (fun _ => 0) v hAbs
  exact ⟨v,hv,fun g => by simpa only [sub_zero] using hS g⟩

end ActualGlobalTraceTorsionSupported318

#print axioms ActualGlobalTraceTorsionSupported318.supported_mul_trace_torsion
