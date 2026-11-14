module
public import ActualOriginalPrimitiveInfinitude318
public import Mathlib.Data.Set.Finite.Basic
public section
noncomputable section
namespace ActualOriginalIndexedPrimitiveSource318
open QuadricCRTAssembly318 ActualOriginalPrimitiveRegionRays318 ActualOriginalPrimitiveInfinitude318
open ActualPrimePointPrimitivity318 ActualPrimitiveSourceRestriction318
open ActualOriginalPositiveRealPoint318 ActualOriginalIntegerTiling318 OriginalWeightedSelberg318

/-- An actual injective family of original globally primitive points,
with every original integer homogeneous form positive at the SAME point.
No prime-valued, Gaussian-ray or reduction-order property is asserted. -/
theorem actual_indexed_primitive_source {J : Type*} [Fintype J] [DecidableEq J]
    (κ : ℤ) (γ : J → ℤ)
    (hi : (goodPrimitivePoints κ (fun j => (γ j : ℝ))).Infinite) :
    ∃ v : ℕ → Quadric κ, Function.Injective v ∧
      (∀ n, Primitive κ (v n) ∧ 0<(v n).1.1.1 ∧ 0<(v n).1.2.1.1 ∧ 0<(v n).1.2.2 ∧
        ∀ j,0<form κ γ j (v n)) := by
  let e := Set.Infinite.natEmbedding (goodPrimitivePoints κ (fun j => (γ j : ℝ))) hi
  let v : ℕ → Quadric κ := fun n => (e n).1
  refine ⟨v,Subtype.val_injective.comp e.injective,fun n => ?_⟩
  have hh := (e n).2
  have hreg := hh.2
  have ha : (0 : ℝ)<((v n).1.1.1 : ℝ) := hreg.1
  have hc : (0 : ℝ)<((v n).1.2.1.1 : ℝ) := hreg.2.1
  have hw : (0 : ℝ)<((v n).1.2.2 : ℝ) := hreg.2.2.1
  refine ⟨hh.1,by exact_mod_cast ha,by exact_mod_cast hc,by exact_mod_cast hw,fun j => ?_⟩
  have hf := hreg.2.2.2 j
  have he : originalForm (γ j : ℝ) (integerEmbed (v n).1)=(form κ γ j (v n) : ℝ) := by
    simp [originalForm,integerEmbed,form]
  rw [he] at hf
  exact_mod_cast hf

/-- Every finite initial source is genuinely primitive at ALL primes,
with exact requested cardinality. This supplies the old primitive sieve
carrier without assuming any positive prime-value mass. -/
lemma actual_indexed_primitive_finite_source (κ : ℤ) (v : ℕ → Quadric κ)
    (hv : Function.Injective v) (hp : ∀ n,Primitive κ (v n)) (M : ℕ) :
    ((Finset.range M).image v).card=M ∧
      primitiveSource κ ((Finset.range M).image v)=(Finset.range M).image v := by
  classical
  refine ⟨by rw [Finset.card_image_of_injective _ hv,Finset.card_range],?_⟩
  apply Finset.filter_eq_self.mpr
  intro u hu
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
  exact hp n

theorem actual318_indexed_primitive_source {J : Type*} [Fintype J] [DecidableEq J] (γ : J → ℤ) :
    ∃ v : ℕ → Quadric (318 : ℤ), Function.Injective v ∧
      (∀ n,Primitive 318 (v n) ∧ 0<(v n).1.1.1 ∧ 0<(v n).1.2.1.1 ∧ 0<(v n).1.2.2 ∧
        ∀ j,0<form 318 γ j (v n)) :=
  actual_indexed_primitive_source 318 γ (actual318_primitive_infinitely_many (fun j => (γ j : ℝ)))

theorem actual326_indexed_primitive_source {J : Type*} [Fintype J] [DecidableEq J] (γ : J → ℤ) :
    ∃ v : ℕ → Quadric (326 : ℤ), Function.Injective v ∧
      (∀ n,Primitive 326 (v n) ∧ 0<(v n).1.1.1 ∧ 0<(v n).1.2.1.1 ∧ 0<(v n).1.2.2 ∧
        ∀ j,0<form 326 γ j (v n)) :=
  actual_indexed_primitive_source 326 γ (actual326_primitive_infinitely_many (fun j => (γ j : ℝ)))

end ActualOriginalIndexedPrimitiveSource318
