module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public section

namespace FiniteInvolutionPrimaryCore318

variable {G : Type*} [CommGroup G]

private theorem root_at_lower_level {x z : G} {k N : ℕ} (hk : k ≤ N)
    (hz : z ^ (2^N : ℕ) = x) : ∃ y : G, y ^ (2^k : ℕ) = x := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
  have hpow : (2^N : ℕ) = 2^d * 2^k := by rw [hd, pow_add, mul_comm]
  exact ⟨z ^ (2^d : ℕ), by rw [← pow_mul, ← hpow, hz]⟩

/-- A finite square kernel, not a finite ambient group, is sufficient to find
one square root of infinite dyadic depth. There is no cardinal-two bound. -/
theorem exists_square_root_at_all_levels (hFin : Finite ((powMonoidHom (α := G) 2).ker))
    {x : G} (hx : ∀ k : ℕ, ∃ z : G, z ^ (2^k : ℕ) = x) :
    ∃ y : G, y ^ 2 = x ∧ ∀ k : ℕ, ∃ z : G, z ^ (2^k : ℕ) = y := by
  classical
  obtain ⟨r,hr₀⟩ := hx 1
  have hr : r ^ 2 = x := by simpa only [pow_one] using hr₀
  let F := {y : G // y ^ 2 = x}
  let f : F → (powMonoidHom (α := G) 2).ker := fun y =>
    ⟨y.val * r⁻¹, by
      change (y.val * r⁻¹) ^ 2 = 1
      rw [mul_pow, inv_pow, y.property, hr, mul_inv_cancel]⟩
  letI : Finite ((powMonoidHom (α := G) 2).ker) := hFin
  haveI : Finite F := Finite.of_injective f (by
    intro y z h
    apply Subtype.ext
    have h' : y.val * r⁻¹ = z.val * r⁻¹ := congrArg Subtype.val h
    exact mul_right_cancel h')
  letI : Fintype F := Fintype.ofFinite F
  by_contra h
  have hbad (y : F) : ∃ k : ℕ, ¬ ∃ z : G, z ^ (2^k : ℕ) = y.val := by
    by_contra hy
    apply h
    refine ⟨y.val, y.property, ?_⟩
    intro k
    by_contra hz
    exact hy ⟨k,hz⟩
  let depth (y : F) : ℕ := Classical.choose (hbad y)
  let N := (Finset.univ : Finset F).sup depth
  obtain ⟨z,hz⟩ := hx (N+1)
  let y : F := ⟨z ^ (2^N : ℕ), by rw [← pow_mul, ← pow_succ, hz]⟩
  have hle : depth y ≤ N := Finset.le_sup (Finset.mem_univ y)
  exact Classical.choose_spec (hbad y) (root_at_lower_level hle (show z ^ (2^N : ℕ) = y.val from rfl))

/-- If a dyadic-primary group has finite two-torsion, any subgroup defined by
infinite dyadic height is exactly its largest divisible subgroup. The subgroup C
is passed in, so the project keeps its existing definition of stableTwoCore. -/
theorem maximal_divisible_of_finite_involutions
    (hP : IsPGroup 2 G) (hFin : Finite ((powMonoidHom (α := G) 2).ker))
    (C : Subgroup G) (hC : ∀ x : G, x ∈ C ↔ ∀ k : ℕ, ∃ z : G, z ^ (2^k : ℕ) = x) :
    (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : C => x ^ m)) ∧
      ∀ D : Subgroup G,
        (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : D => x ^ m)) → D ≤ C := by
  have hSq (x : C) : ∃ r : C, r ^ 2 = x := by
    obtain ⟨r,hr,hDepth⟩ := exists_square_root_at_all_levels hFin ((hC x.val).mp x.property)
    exact ⟨⟨r,(hC r).mpr hDepth⟩,Subtype.ext hr⟩
  have hDepth (k : ℕ) (x : C) : ∃ r : C, r ^ (2^k : ℕ) = x := by
    induction k generalizing x with
    | zero => exact ⟨x,by simp⟩
    | succ k ih =>
      obtain ⟨s,hs⟩ := hSq x
      obtain ⟨r,hr⟩ := ih s
      exact ⟨r,by rw [pow_succ, pow_mul, hr, hs]⟩
  have hPC : IsPGroup 2 C := isPGroup_iff_pow_pow_eq_one.mpr (fun x => by
    obtain ⟨k,hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hP x.val
    exact ⟨k,Subtype.ext hk⟩)
  constructor
  · intro m hm
    obtain ⟨k,a,ha,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
    intro x
    let e := hPC.powEquiv (Nat.coprime_two_left.mpr ha)
    obtain ⟨s,hs⟩ := e.surjective x
    obtain ⟨r,hr⟩ := hDepth k s
    exact ⟨r,by
      change r ^ (2^k * a) = x
      rw [pow_mul,hr]
      dsimp only [e] at hs
      rw [IsPGroup.powEquiv_apply] at hs
      exact hs⟩
  · intro D hD x hx
    apply (hC x).mpr
    intro k
    obtain ⟨y,hy⟩ := hD (2^k) (pow_ne_zero _ (by decide)) ⟨x,hx⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

end FiniteInvolutionPrimaryCore318
