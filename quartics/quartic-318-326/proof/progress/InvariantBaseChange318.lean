module

public import OrbitAlgebra318
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Etale.Descent

@[expose] public section

noncomputable section

open TensorProduct

namespace InvariantBaseChange318

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable {G : Type*}

/-- The simultaneous fixed algebra of a family of actual algebra automorphisms. -/
def invariants (ρ : G → B ≃ₐ[R] B) : Subalgebra R B where
  carrier := {b | ∀ g, ρ g b = b}
  mul_mem' hx hy g := by simp only [map_mul, hx g, hy g]
  one_mem' := by simp
  add_mem' hx hy g := by simp only [map_add, hx g, hy g]
  zero_mem' := by simp
  algebraMap_mem' r := by simp

/-- All fixed equations are encoded by one linear map, not an averaging projector. -/
def difference (ρ : G → B ≃ₐ[R] B) : B →ₗ[R] (G → B) :=
  LinearMap.pi fun g => (ρ g).toLinearMap - LinearMap.id

@[simp] theorem difference_apply (ρ : G → B ≃ₐ[R] B) (b : B) (g : G) :
    difference ρ b g = ρ g b - b := rfl

theorem mem_invariants_iff (ρ : G → B ≃ₐ[R] B) (b : B) :
    b ∈ invariants ρ ↔ difference ρ b = 0 := by
  change (∀ g, ρ g b = b) ↔ _
  simp only [funext_iff, difference_apply, Pi.zero_apply, sub_eq_zero]

/-- Fixed equations are exact with their actual inclusion. -/
theorem invariant_exact (ρ : G → B ≃ₐ[R] B) :
    Function.Exact (invariants ρ).val.toLinearMap (difference ρ) := by
  intro b
  change difference ρ b = 0 ↔ ∃ a : invariants ρ, (a : B) = b
  rw [← mem_invariants_iff]
  exact ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.property⟩

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The actual scalar-extended automorphisms on the tensor-product algebra. -/
def baseAction (ρ : G → B ≃ₐ[R] B) (g : G) :
    S ⊗[R] B ≃ₐ[S] S ⊗[R] B :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (ρ g)

@[simp] theorem baseAction_tmul (ρ : G → B ≃ₐ[R] B) (g : G) (s : S) (b : B) :
    baseAction S ρ g (s ⊗ₜ[R] b) = s ⊗ₜ[R] ρ g b := rfl

/-- Inclusion of the scalar extension of the fixed algebra into the full algebra. -/
def inclusion (ρ : G → B ≃ₐ[R] B) :
    S ⊗[R] invariants ρ →ₐ[S] S ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) (invariants ρ).val

@[simp] theorem inclusion_tmul (ρ : G → B ≃ₐ[R] B) (s : S) (b : invariants ρ) :
    inclusion S ρ (s ⊗ₜ[R] b) = s ⊗ₜ[R] (b : B) := rfl

/-- The tensor inclusion satisfies the fixed equations term by term. -/
theorem inclusion_fixed (ρ : G → B ≃ₐ[R] B) (a : S ⊗[R] invariants ρ) :
    inclusion S ρ a ∈ invariants (baseAction S ρ) := by
  intro g
  induction a using TensorProduct.inductionOn with
  | tmul s b => simp only [inclusion_tmul, baseAction_tmul, b.property g]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical flat-base-change map for the actual invariant algebra. -/
def canonical (ρ : G → B ≃ₐ[R] B) :
    S ⊗[R] invariants ρ →ₐ[S] invariants (baseAction S ρ) :=
  (inclusion S ρ).codRestrict _ (inclusion_fixed S ρ)

/-- Tensoring the finite system of fixed equations is the system of fixed equations
for the base-changed action. Finiteness is used only for tensor/product commutation. -/
theorem difference_baseChange [Fintype G] [DecidableEq G] (ρ : G → B ≃ₐ[R] B) :
    difference (baseAction S ρ) =
      (TensorProduct.piRight R S S (fun _ : G => B)).toLinearMap.comp
        (AlgebraTensorModule.lTensor S S (difference ρ)) := by
  ext b g
  simp [difference_apply, TensorProduct.tmul_sub]

/-- The canonical invariant-base-change map is injective for flat base change. -/
theorem canonical_injective [Module.Flat R S] (ρ : G → B ≃ₐ[R] B) :
    Function.Injective (canonical S ρ) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    (M := S) (invariants ρ).val.toLinearMap Subtype.val_injective
  intro a b h
  apply hi
  exact congrArg Subtype.val h

/-- The canonical invariant-base-change map is surjective for finite families
and flat base change, including when the group order is not invertible. -/
theorem canonical_surjective [Finite G] [Module.Flat R S] (ρ : G → B ≃ₐ[R] B) :
    Function.Surjective (canonical S ρ) := by
  classical
  letI := Fintype.ofFinite G
  intro x
  have hx : difference (baseAction S ρ) (x : S ⊗[R] B) = 0 :=
    (mem_invariants_iff _ _).mp x.property
  rw [difference_baseChange S ρ, LinearMap.comp_apply] at hx
  have hz : AlgebraTensorModule.lTensor S S (difference ρ) (x : S ⊗[R] B) = 0 :=
    (TensorProduct.piRight R S S (fun _ : G => B)).injective (by simpa using hx)
  obtain ⟨a, ha⟩ := (Module.Flat.lTensor_exact S (invariant_exact ρ) x).mp hz
  exact ⟨a, Subtype.ext ha⟩

/-- Actual invariants of a finite automorphism family commute with flat base change. -/
def baseChangeEquiv [Finite G] [Module.Flat R S] (ρ : G → B ≃ₐ[R] B) :
    S ⊗[R] invariants ρ ≃ₐ[S] invariants (baseAction S ρ) :=
  AlgEquiv.ofBijective (canonical S ρ)
    ⟨canonical_injective S ρ, canonical_surjective S ρ⟩

@[simp] theorem baseChangeEquiv_tmul [Finite G] [Module.Flat R S]
    (ρ : G → B ≃ₐ[R] B) (s : S) (b : invariants ρ) :
    (baseChangeEquiv S ρ (s ⊗ₜ[R] b)).1 = s ⊗ₜ[R] (b : B) := rfl

end InvariantBaseChange318
