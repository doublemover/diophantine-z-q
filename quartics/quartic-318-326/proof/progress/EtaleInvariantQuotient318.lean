module

public import InvariantBaseChange318

@[expose] public section

noncomputable section

open TensorProduct
open InvariantBaseChange318

namespace EtaleInvariantQuotient318

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable {G X : Type*} [Group G] [MulAction G X]

/-- An actual equivariant splitting identifies the fixed algebra with functions
on the actual orbit set, not with an assumed quotient algebra. -/
def splitInvariantEquiv (ρ : G → B ≃ₐ[R] B) (e : B ≃ₐ[R] (X → R))
    (he : ∀ (g : G) (b : B) (x : X), e (ρ g b) x = e b (g • x)) :
    invariants ρ ≃ₐ[R] OrbitAlgebra318.fixedFunctions R G X where
  toFun b := ⟨e b, by
    intro g x
    rw [← he, b.property g]⟩
  invFun f := ⟨e.symm f, by
    intro g
    apply e.injective
    ext x
    rw [he, e.apply_symm_apply]
    exact f.property g x⟩
  left_inv b := by apply Subtype.ext; exact e.symm_apply_apply b
  right_inv f := by apply Subtype.ext; exact e.apply_symm_apply f
  map_mul' b c := by apply Subtype.ext; exact e.map_mul b c
  map_add' b c := by apply Subtype.ext; exact e.map_add b c
  commutes' r := by apply Subtype.ext; exact e.commutes r

/-- Finite étaleness of the actual invariant algebra after an equivariant split. -/
theorem split_finite_etale [Finite X]
    (ρ : G → B ≃ₐ[R] B) (e : B ≃ₐ[R] (X → R))
    (he : ∀ (g : G) (b : B) (x : X), e (ρ g b) x = e b (g • x)) :
    Module.Finite R (invariants ρ) ∧ Algebra.Etale R (invariants ρ) := by
  let q := (splitInvariantEquiv ρ e he).symm
  exact ⟨Module.Finite.equiv q.toLinearEquiv, Algebra.Etale.of_equiv q⟩

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Explicit scalar-extended invariant algebra as the orbit-coordinate algebra. -/
def splitBaseChangeEquiv [Finite G] [Module.Flat R S]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x)) :
    S ⊗[R] invariants ρ ≃ₐ[S] (OrbitAlgebra318.Orbits G X → S) :=
  (baseChangeEquiv S ρ).trans <|
    (splitInvariantEquiv (baseAction S ρ) e he).trans
      (OrbitAlgebra318.orbitEquiv S G X).symm

/-- The actual finite étale invariant quotient descends from any faithfully flat
 equivariant splitting. In particular |G| is not required to be a unit. -/
theorem finite_etale_of_faithfullyFlat_split [Finite G] [Finite X]
    [Module.FaithfullyFlat R S]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x)) :
    Module.Finite R (invariants ρ) ∧ Algebra.Etale R (invariants ρ) := by
  let q := (splitBaseChangeEquiv S ρ e he).symm
  letI : Module.Finite S (S ⊗[R] invariants ρ) :=
    Module.Finite.equiv q.toLinearEquiv
  letI : Algebra.Etale S (S ⊗[R] invariants ρ) := Algebra.Etale.of_equiv q
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat S⟩

/-- The original cover itself is finite étale from the same actual splitting. -/
theorem cover_finite_etale [Finite X] [Module.FaithfullyFlat R S]
    (e : S ⊗[R] B ≃ₐ[S] (X → S)) :
    Module.Finite R B ∧ Algebra.Etale R B := by
  letI : Module.Finite S (S ⊗[R] B) := Module.Finite.equiv e.symm.toLinearEquiv
  letI : Algebra.Etale S (S ⊗[R] B) := Algebra.Etale.of_equiv e.symm
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat S⟩

/-- The original cover is also finite étale over the actual quotient algebra. -/
theorem quotient_map_finite_etale [Finite G] [Finite X] [Module.FaithfullyFlat R S]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x)) :
    Module.Finite (invariants ρ) B ∧ Algebra.Etale (invariants ρ) B := by
  obtain ⟨hBf, hBe⟩ := cover_finite_etale S e
  obtain ⟨hIf, hIe⟩ := finite_etale_of_faithfullyFlat_split S ρ e he
  letI := hBf
  letI := hBe
  letI := hIf
  letI := hIe
  exact ⟨Module.Finite.of_restrictScalars_finite R (invariants ρ) B,
    Algebra.Etale.of_restrictScalars R (invariants ρ) B⟩

/-- Base extension of the constructed quotient remains finite étale. This
includes arbitrary number-ring base change; flatness of the new map is not needed. -/
theorem quotient_baseChange_finite_etale [Finite G] [Finite X]
    [Module.FaithfullyFlat R S]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x))
    (T : Type*) [CommRing T] [Algebra R T] :
    Module.Finite T (T ⊗[R] invariants ρ) ∧ Algebra.Etale T (T ⊗[R] invariants ρ) := by
  obtain ⟨hf, he'⟩ := finite_etale_of_faithfullyFlat_split S ρ e he
  letI := hf
  letI := he'
  exact ⟨inferInstance, inferInstance⟩

section UniversalProperty
variable {C : Type*} [CommRing C] [Algebra R C]

/-- The actual factor through the invariant algebra for an invariant map. -/
def factor (ρ : G → B ≃ₐ[R] B) (f : C →ₐ[R] B)
    (hf : ∀ g c, ρ g (f c) = f c) : C →ₐ[R] invariants ρ :=
  f.codRestrict _ (fun c g => hf g c)

@[simp] theorem factor_comp (ρ : G → B ≃ₐ[R] B) (f : C →ₐ[R] B)
    (hf : ∀ g c, ρ g (f c) = f c) :
    (invariants ρ).val.comp (factor ρ f hf) = f := rfl

/-- The affine quotient universal property, with existence and uniqueness. -/
theorem existsUnique_factor (ρ : G → B ≃ₐ[R] B) (f : C →ₐ[R] B)
    (hf : ∀ g c, ρ g (f c) = f c) :
    ∃! q : C →ₐ[R] invariants ρ, (invariants ρ).val.comp q = f := by
  refine ⟨factor ρ f hf, rfl, ?_⟩
  intro q hq
  ext c
  exact congrArg (fun h : C →ₐ[R] B => h c) hq

end UniversalProperty

end EtaleInvariantQuotient318
