module
public import OriginalRetainedDirichlet318
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public section
noncomputable section
namespace OriginalFiniteLabelRankin318
open scoped BigOperators
open OriginalUniformGoodFamily318 OriginalRetainedFamilyWeight318 OriginalRetainedDirichlet318
set_option maxHeartbeats 8000000

@[expose] def localProduct (κ : ℤ) (δ : ℝ) (B : ℕ) : ℝ :=
  ∏ p∈(Finset.range (B+1)).filter Nat.Prime, localFactor κ δ p

/-- Every positive original label<=B is supported on the actual finite
prime range. Its injective inclusion into the Euler sum is constructed. -/
lemma finite_dirichlet_bound (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (B : ℕ) :
    (∑ n∈Finset.Icc 1 B, dirichlet κ δ n)≤localProduct κ δ B := by
  classical
  let f : ↥(Finset.Icc 1 B) → Nat.factoredNumbers (Finset.range (B+1)) := fun n =>
    ⟨n.1,Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by have hh := Finset.mem_Icc.mp n.2;omega,
      fun p hpn _ _ => Finset.mem_range.mpr (by have hh := Finset.mem_Icc.mp n.2;omega)⟩⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hh := hasSum_le_inj f hf (fun n _ => nonneg κ δ n.1) (fun _ => le_rfl)
    (hasSum_fintype (fun n : ↥(Finset.Icc 1 B) => dirichlet κ δ n.1))
    (finite_euler κ δ hδ (Finset.range (B+1)))
  simpa only [Finset.sum_coe_sort,localProduct] using hh

/-- The actual positive-label sum is bounded by a finite Euler product
of the exact retained-radical weight. This is a genuine Rankin step, not
a supplied label-average or prime-distribution estimate. -/
theorem actual_finite_rankin (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (B : ℕ) :
    (∑ n∈Finset.Icc 1 B, familyWeight κ (n:ℤ))≤(B:ℝ)^δ*localProduct κ δ B := by
  have hterm (n : ℕ) (hn : n∈Finset.Icc 1 B) :
      familyWeight κ (n:ℤ)≤(B:ℝ)^δ*dirichlet κ δ n := by
    have hn0 : n≠0 := by have hh := Finset.mem_Icc.mp hn;omega
    have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hle : (n:ℝ)≤B := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hr := Real.rpow_le_rpow hnR.le hle hδ.le
    have he : dirichlet κ δ n*(n:ℝ)^δ=weight κ n := by
      dsimp [dirichlet]
      rw [mul_assoc,←Real.rpow_add hnR]
      simp
    rw [←actual_weight κ n hn0,←he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr (nonneg κ δ n)
  have hh := Finset.sum_le_sum (fun n hn => hterm n hn)
  calc
    _ ≤ ∑ n∈Finset.Icc 1 B, (B:ℝ)^δ*dirichlet κ δ n := hh
    _ = (B:ℝ)^δ*(∑ n∈Finset.Icc 1 B, dirichlet κ δ n) := (Finset.mul_sum _ _ _).symm
    _ ≤ (B:ℝ)^δ*localProduct κ δ B :=
      mul_le_mul_of_nonneg_left (finite_dirichlet_bound κ δ hδ B) (Real.rpow_nonneg (Nat.cast_nonneg B) _)

end OriginalFiniteLabelRankin318
