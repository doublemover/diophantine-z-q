module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public section
noncomputable section
namespace SquareZeroProjectiveGenerator318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {S : Type u} {R : Type v} [CommRing S] [CommRing R]
    (π : S →+* R) (σ : R →+* S) (hσ : ∀ r, π (σ r) = r)
    (e : S) (he : e * e = 0)
    (hπ : ∀ s : S, π s = 0 → ∃ r : S, e * r = s)
    {P : Type w} [AddCommGroup P] [Module S P]
    (γ : P →+ R) (hγ : ∀ s : S, ∀ x : P, γ (s • x) = π s * γ x)
    (hker : ∀ x : P, γ x = 0 → ∃ y : P, e • y = x)
    (p : P) (hp : γ p = 1)
include hσ he hγ hker hp in
/-- For a square-zero kernel, two explicit reductions replace Nakayama:
a lift of the reduced generator already generates the entire original module. -/
lemma spans (x : P) : ∃ s : S, s • p = x := by
  have hx : γ (x - σ (γ x) • p) = 0 := by
    rw [map_sub, hγ, hσ, hp, mul_one, sub_self]
  obtain ⟨y,hy⟩ := hker _ hx
  have hy0 : γ (y - σ (γ y) • p) = 0 := by
    rw [map_sub, hγ, hσ, hp, mul_one, sub_self]
  obtain ⟨z,hz⟩ := hker _ hy0
  refine ⟨σ (γ x) + e * σ (γ y), ?_⟩
  have hy' : y = σ (γ y) • p + e • z := by rw [hz]; abel
  have hx' : x = σ (γ x) • p + e • y := by rw [hy]; abel
  calc
    (σ (γ x) + e * σ (γ y)) • p =
        σ (γ x) • p + e • (σ (γ y) • p + e • z) := by
      simp only [add_smul, smul_add, ← mul_smul, he, zero_smul, add_zero]
    _ = σ (γ x) • p + e • y := by rw [← hy']
    _ = x := hx'.symm
include he hπ in
lemma unit_of_reduction_one (s : S) (hs : π s = 1) : IsUnit s := by
  obtain ⟨r,hr⟩ := hπ (s - 1) (by rw [map_sub, hs, map_one, sub_self])
  have hs' : s = 1 + e * r := by rw [hr]; ring
  refine ⟨⟨s, 1 - e * r, ?_, ?_⟩, rfl⟩
  · rw [hs']
    calc
      (1 + e * r) * (1 - e * r) = 1 - (e * e) * (r * r) := by ring
      _ = 1 := by rw [he]; ring
  · rw [hs']
    calc
      (1 - e * r) * (1 + e * r) = 1 - (e * e) * (r * r) := by ring
      _ = 1 := by rw [he]; ring
@[expose] def generatorMap : S →ₗ[S] P := LinearMap.toSpanSingleton S P p
include hσ he hγ hker hp in
lemma generator_surjective : Function.Surjective (generatorMap p) :=
  spans π σ hσ e he γ hγ hker p hp
include hσ he hπ hγ hker hp in
/-- Projectivity supplies an actual splitting; its scalar on the generator
reduces to one and is therefore a unit. This proves injectivity, not just spanning. -/
lemma generator_injective [Module.Projective S P] : Function.Injective (generatorMap p) := by
  obtain ⟨g,hg⟩ := Module.projective_lifting_property (generatorMap p) (LinearMap.id : P →ₗ[S] P)
    (generator_surjective π σ hσ e he γ hγ hker p hp)
  have hgp : (g p) • p = p := DFunLike.congr_fun hg p
  have hred : π (g p) = 1 := by
    have hh := congrArg γ hgp
    rw [hγ, hp, mul_one] at hh
    exact hh
  obtain ⟨u,hu⟩ := unit_of_reduction_one π e he hπ (g p) hred
  intro s t hst
  have hh := congrArg g hst
  change g (s • p) = g (t • p) at hh
  rw [map_smul, map_smul] at hh
  change s * g p = t * g p at hh
  rw [← hu] at hh
  have hi := congrArg (fun z : S => z * u.inv) hh
  simpa only [mul_assoc, u.val_inv, mul_one] using hi
/-- An actual rank-one basis map lifting the SPECIFIED reduced generator.
The future affine consumer must supply the literal reduction and its ε-kernel. -/
@[expose] def equivalence [Module.Projective S P] : S ≃ₗ[S] P :=
  LinearEquiv.ofBijective (generatorMap p)
    ⟨generator_injective π σ hσ e he hπ γ hγ hker p hp,
      generator_surjective π σ hσ e he γ hγ hker p hp⟩
lemma equivalence_one [Module.Projective S P] : equivalence π σ hσ e he hπ γ hγ hker p hp 1 = p :=
  one_smul S p
end SquareZeroProjectiveGenerator318
