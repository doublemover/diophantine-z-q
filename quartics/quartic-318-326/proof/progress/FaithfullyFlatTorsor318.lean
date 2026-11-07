module

public import FreeOrbitAlgebra318
public import InvariantBaseChange318

@[expose] public section

noncomputable section

open TensorProduct

namespace FaithfullyFlatTorsor318

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [Fintype G]

/-- The genuine canonical torsor coordinate map, defined from the actual action. -/
def canonical (ρ : G → B ≃ₐ[A] B) : B ⊗[A] B →ₐ[A] (G → B) :=
  AlgHom.pi fun g => Algebra.TensorProduct.lift (AlgHom.id A B) (ρ g).toAlgHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem canonical_tmul (ρ : G → B ≃ₐ[A] B) (b c : B) (g : G) :
    canonical ρ (b ⊗ₜ[A] c) g = b * ρ g c := rfl

/-- The actual canonical torsor isomorphism for the regular split cover. -/
def regularEquiv (A : Type*) [CommRing A] (G : Type*) [Group G] [Fintype G] :
    (G → A) ⊗[A] (G → A) ≃ₐ[A] (G → G → A) := by
  classical
  exact (Algebra.TensorProduct.piScalarRight A A (G → A) G).trans
    (FreeOrbitAlgebra318.matrixTwist G A)

@[simp] theorem regularEquiv_tmul (b c : G → A) (g h : G) :
    regularEquiv A G (b ⊗ₜ[A] c) g h = b h * c (g*h) := by
  change c (g*h) * b h = _
  exact mul_comm _ _

/-- Transport the actual regular torsor isomorphism along a genuine algebra splitting. -/
def splitEquiv (e : B ≃ₐ[A] (G → A)) : B ⊗[A] B ≃ₐ[A] (G → B) :=
  (Algebra.TensorProduct.congr e e).trans <|
    (regularEquiv A G).trans (AlgEquiv.piCongrRight (fun _ : G => e.symm))

theorem splitEquiv_tmul (e : B ≃ₐ[A] (G → A)) (b c : B) (g : G) :
    splitEquiv e (b ⊗ₜ[A] c) g = e.symm (fun h => e b h * e c (g*h)) := by
  change e.symm (fun h => e c (g*h) * e b h) = _
  congr 1
  funext h
  exact mul_comm _ _

/-- Exact equivariance identifies the constructed isomorphism with the canonical map. -/
theorem splitEquiv_eq_canonical (ρ : G → B ≃ₐ[A] B) (e : B ≃ₐ[A] (G → A))
    (he : ∀ (g : G) (b : B) (h : G), e (ρ g b) h = e b (g*h)) :
    (splitEquiv e).toAlgHom = canonical ρ := by
  apply Algebra.TensorProduct.ext'
  intro b c
  funext g
  rw [AlgEquiv.coe_toAlgHom, splitEquiv_tmul, canonical_tmul]
  apply e.injective
  rw [e.apply_symm_apply, map_mul]
  funext h
  simp only [Pi.mul_apply, he]

theorem canonical_bijective_of_split (ρ : G → B ≃ₐ[A] B)
    (e : B ≃ₐ[A] (G → A))
    (he : ∀ (g : G) (b : B) (h : G), e (ρ g b) h = e b (g*h)) :
    Function.Bijective (canonical ρ) := by
  rw [← splitEquiv_eq_canonical ρ e he]
  exact (splitEquiv e).bijective

section Descent

variable (S : Type*) [CommRing S] [Algebra A S]

/-- The actual associativity/base-change isomorphism for the two tensor factors. -/
def doubleBaseEquiv :
    S ⊗[A] (B ⊗[A] B) ≃ₐ[S] (S ⊗[A] B) ⊗[S] (S ⊗[A] B) :=
  (Algebra.TensorProduct.assoc A A S S B B).symm.trans
    (Algebra.TensorProduct.cancelBaseChange A S S (S ⊗[A] B) B).symm

@[simp] theorem doubleBaseEquiv_tmul (s : S) (b c : B) :
    doubleBaseEquiv (A := A) (B := B) S (s ⊗ₜ[A] (b ⊗ₜ[A] c)) =
      (s ⊗ₜ[A] b) ⊗ₜ[S] (1 ⊗ₜ[A] c) := rfl

/-- The canonical torsor map itself, not just its source and target, commutes
with actual scalar extension under the canonical tensor/product identifications. -/
theorem canonical_baseChange [DecidableEq G] (ρ : G → B ≃ₐ[A] B) :
    (Algebra.TensorProduct.piRight A S S (fun _ : G => B)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) (canonical ρ)) =
    (canonical (InvariantBaseChange318.baseAction S ρ)).comp
      (doubleBaseEquiv (A := A) (B := B) S).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    ext g
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.piRight_tmul, doubleBaseEquiv_tmul,
      canonical_tmul, InvariantBaseChange318.baseAction_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add z w hz hw =>
    simp only [TensorProduct.tmul_add, map_add, hz, hw]

/-- Faithfully flat descent of the exact canonical torsor map from an actual
regular equivariant splitting. No isomorphism or torsor-law premise is supplied. -/
theorem canonical_bijective_of_faithfullyFlat_split [Module.FaithfullyFlat A S]
    (ρ : G → B ≃ₐ[A] B) (e : S ⊗[A] B ≃ₐ[S] (G → S))
    (he : ∀ (g : G) (b : S ⊗[A] B) (h : G),
      e (InvariantBaseChange318.baseAction S ρ g b) h = e b (g*h)) :
    Function.Bijective (canonical ρ) := by
  classical
  have hb := canonical_bijective_of_split (InvariantBaseChange318.baseAction S ρ) e he
  have hd := (doubleBaseEquiv (A := A) (B := B) S).bijective
  have hc := hb.comp hd
  let P := Algebra.TensorProduct.piRight A S S (fun _ : G => B)
  let F := Algebra.TensorProduct.map (AlgHom.id S S) (canonical ρ)
  have hcomp : Function.Bijective (P.toAlgHom.comp F) := by
    rw [show P.toAlgHom.comp F =
      (canonical (InvariantBaseChange318.baseAction S ρ)).comp
        (doubleBaseEquiv (A := A) (B := B) S).toAlgHom from canonical_baseChange S ρ]
    exact hc
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      apply hcomp.injective
      exact congrArg P hxy
    · intro y
      obtain ⟨x, hx⟩ := hcomp.surjective (P y)
      exact ⟨x, P.injective hx⟩
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    A S (canonical ρ).toLinearMap).mp hF

/-- The descended genuine torsor algebra equivalence. -/
def torsorEquiv_of_faithfullyFlat_split [Module.FaithfullyFlat A S]
    (ρ : G → B ≃ₐ[A] B) (e : S ⊗[A] B ≃ₐ[S] (G → S))
    (he : ∀ (g : G) (b : S ⊗[A] B) (h : G),
      e (InvariantBaseChange318.baseAction S ρ g b) h = e b (g*h)) :
    B ⊗[A] B ≃ₐ[A] (G → B) :=
  AlgEquiv.ofBijective (canonical ρ)
    (canonical_bijective_of_faithfullyFlat_split S ρ e he)

@[simp] theorem descended_tmul [Module.FaithfullyFlat A S]
    (ρ : G → B ≃ₐ[A] B) (e : S ⊗[A] B ≃ₐ[S] (G → S))
    (he : ∀ (g : G) (b : S ⊗[A] B) (h : G),
      e (InvariantBaseChange318.baseAction S ρ g b) h = e b (g*h))
    (b c : B) (g : G) :
    torsorEquiv_of_faithfullyFlat_split S ρ e he (b ⊗ₜ[A] c) g = b * ρ g c := rfl

end Descent

end FaithfullyFlatTorsor318
