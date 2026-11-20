module
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
public section

namespace ActualSupportedPrimitiveRetention318

variable {G Γ A : Type*} [Group G] [Group Γ] [AddCommGroup A]

/-- Both chosen cocycles, and the actual action on the finite torsion,
are already supported. Equality on the original absolute group gives
equality on this very support quotient with the very same primitive. -/
theorem supported_boundary (π : G →* Γ) (hπ : Function.Surjective π)
    (ρ : Γ →* AddMonoid.End A) (z z₀ : Γ → A) (w : A)
    (hw : ∀ g, z (π g) - z₀ (π g) = ρ (π g) w - w) :
    ∀ g, z g - z₀ g = ρ g w - w := by
  intro g
  obtain ⟨x, hx⟩ := hπ g
  simpa only [hx] using hw x

/-- No change of representative of either cocycle is allowed here.
The difference of two possible global primitives is an invariant. -/
theorem primitive_difference_fixed (ρ : Γ →* AddMonoid.End A) (z : Γ → A)
    (w w' : A) (hw : ∀ g, z g = ρ g w - w) (hw' : ∀ g, z g = ρ g w' - w') :
    ∀ g, ρ g (w' - w) = w' - w := by
  intro g
  have eq : ρ g w' - w' = ρ g w - w := (hw' g).symm.trans (hw g)
  rw [map_sub]
  calc
    ρ g w' - ρ g w = (ρ g w' - w') - (ρ g w - w) + (w' - w) := by abel
    _ = w' - w := by rw [eq,sub_self,zero_add]

/-- A fixed old local primitive t is not reselected when changing the
global primitive by an invariant. The changed local discrepancy is the
restriction of that same invariant, with the plus sign. -/
theorem old_gauge_at (ρ : Γ →* AddMonoid.End A) (z : Γ → A)
    (w w' t : A) (hw : ∀ g, z g = ρ g w - w) (hw' : ∀ g, z g = ρ g w' - w')
    (g : Γ) :
    (ρ g w' - t) - (ρ g w - t) = w' - w := by
  rw [show (ρ g w' - t) - (ρ g w - t) = ρ g w' - ρ g w by abel,
      ←map_sub]
  exact primitive_difference_fixed ρ z w w' hw hw' g

abbrev Residue (a : ℕ) := ZMod (2^a)

/-- Finite torsion in the free coefficient lattice loses at most e
bits. This is divisibility inside the residue ring, not division in it. -/
theorem factor_cancelled_power {a e : ℕ} (he : e ≤ a)
    (x : Residue a) (hx : (2 : Residue a)^e * x = 0) :
    ∃ y : Residue a, x = (2 : Residue a)^(a-e) * y := by
  letI : NeZero ((2:ℕ)^a) := ⟨pow_ne_zero _ (by decide)⟩
  have hval : (x.val : Residue a) = x := ZMod.natCast_zmod_val x
  have hbig : (2:ℕ)^a ∣ (2:ℕ)^e * x.val := by
    apply (ZMod.natCast_eq_zero_iff ((2:ℕ)^e * x.val) ((2:ℕ)^a)).mp
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_two,hval,hx]
  have hsum : e + (a-e) = a := by omega
  have hpow : (2:ℕ)^a = (2:ℕ)^e * (2:ℕ)^(a-e) := by rw [←pow_add,hsum]
  rw [hpow] at hbig
  obtain ⟨k,hk⟩ := (mul_dvd_mul_iff_left
    (pow_ne_zero e (by decide : (2:ℕ) ≠ 0))).mp hbig
  refine ⟨(k : Residue a), ?_⟩
  calc
    x = (x.val : Residue a) := hval.symm
    _ = _ := by rw [hk,Nat.cast_mul,Nat.cast_pow,Nat.cast_two]

/-- The same-row ambiguity is small uniformly in the stated bound on
the actual invariant subgroup. The bound is used on finite torsion,
not on all geometric points. No compatibility of prechosen witnesses
at different precisions is assumed. -/
theorem same_row_bounded {ι : Type*} {a e : ℕ} (he : e ≤ a)
    (ρ : Γ →* AddMonoid.End (ι → Residue a))
    (hInv : ∀ x : ι → Residue a, (∀ g, ρ g x = x) →
      ∀ j, (2 : Residue a)^e * x j = 0)
    (z : Γ → ι → Residue a) (w w' : ι → Residue a)
    (hw : ∀ g, z g = ρ g w - w) (hw' : ∀ g, z g = ρ g w' - w') :
    ∃ b : ι → Residue a, w' - w = (2 : Residue a)^(a-e) • b := by
  classical
  have hf := primitive_difference_fixed ρ z w w' hw hw'
  choose b hb using fun j => factor_cancelled_power he ((w'-w) j) (hInv _ hf j)
  refine ⟨b,?_⟩
  funext j
  simpa only [Pi.smul_apply,smul_eq_mul] using hb j

/-- Every prescribed integral linear row carries exactly the same lower
precision bound. No rank on a family of unrelated lift choices is used. -/
theorem integral_row_bound {ι : Type*} {a e : ℕ}
    (ℓ : (ι → Residue a) →ₗ[Residue a] Residue a)
    (w w' b : ι → Residue a) (hb : w'-w = (2 : Residue a)^(a-e) • b) :
    ℓ w' - ℓ w = (2 : Residue a)^(a-e) * ℓ b := by
  rw [←map_sub,hb,map_smul,smul_eq_mul]

end ActualSupportedPrimitiveRetention318

#print axioms ActualSupportedPrimitiveRetention318.supported_boundary
#print axioms ActualSupportedPrimitiveRetention318.same_row_bounded
#print axioms ActualSupportedPrimitiveRetention318.integral_row_bound
