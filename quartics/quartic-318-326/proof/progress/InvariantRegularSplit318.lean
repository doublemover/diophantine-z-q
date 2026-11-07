module

public import TensorTower318
public import EtaleQuotientCover318

@[expose] public section

noncomputable section

open TensorProduct
open InvariantBaseChange318 EtaleInvariantQuotient318 OrbitAlgebra318

namespace InvariantRegularSplit318

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [IsCancelSMul G X]
variable (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
variable (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
variable (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
    e (baseAction S ρ g b) x = e b (g • x))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual action fixes the actual invariant algebra elementwise. -/
def fixedAction (g : G) : B ≃ₐ[invariants ρ] B where
  __ := (ρ g).toRingEquiv
  commutes' a := a.property g

@[simp] theorem fixedAction_apply (g : G) (b : B) : fixedAction ρ g b = ρ g b := rfl

/-- The original splitting with the scalar factor on the right. -/
def coverSplit : B ⊗[R] S ≃ₐ[S] (X → S) :=
  (Algebra.TensorProduct.commRight R S B).symm.trans e

@[simp] theorem coverSplit_tmul (b : B) (s : S) :
    coverSplit S e (b ⊗ₜ[R] s) = e (s ⊗ₜ[R] b) := rfl

/-- Actual invariant base-change and coordinate identification. -/
def invariantSplit : (invariants ρ) ⊗[R] S ≃ₐ[S] fixedFunctions S G X :=
  (Algebra.TensorProduct.commRight R S (invariants ρ)).symm.trans <|
    (baseChangeEquiv S ρ).trans (splitInvariantEquiv (baseAction S ρ) e he)

@[simp] theorem invariantSplit_tmul (a : invariants ρ) (s : S) :
    (invariantSplit S ρ e he (a ⊗ₜ[R] s)).1 = e (s ⊗ₜ[R] (a : B)) := rfl

/-- The two coordinate identifications preserve the actual intermediate inclusion. -/
theorem inclusion_compatible (a : (invariants ρ) ⊗[R] S) :
    coverSplit S e (algebraMap ((invariants ρ) ⊗[R] S) (B ⊗[R] S) a) =
      (invariantSplit S ρ e he a).1 := by
  induction a using TensorProduct.inductionOn with
  | tmul a s => rfl
  | add a b ha hb => simp only [map_add, ha, hb, Subalgebra.coe_add]

/-- The genuine regular splitting over the invariant base, not the original base. -/
def regularSplit : B ⊗[R] S ≃ₐ[(invariants ρ) ⊗[R] S]
    (G → (invariants ρ) ⊗[R] S) :=
  AlgEquiv.ofRingEquiv (f :=
    (coverSplit S e).toRingEquiv.trans <|
      (FreeOrbitAlgebra318.coverEquiv G X S).toRingEquiv.trans <|
        RingEquiv.piCongrRight (fun _ : G => (invariantSplit S ρ e he).symm.toRingEquiv)) (by
    intro a
    funext g
    apply (invariantSplit S ρ e he).injective
    change invariantSplit S ρ e he ((invariantSplit S ρ e he).symm
      (FreeOrbitAlgebra318.coverEquiv G X S
        (coverSplit S e (algebraMap ((invariants ρ) ⊗[R] S) (B ⊗[R] S) a)) g)) =
          invariantSplit S ρ e he a
    rw [AlgEquiv.apply_symm_apply, inclusion_compatible S ρ e he a]
    exact congrFun ((FreeOrbitAlgebra318.coverEquiv G X S).commutes
      (invariantSplit S ρ e he a)) g)

@[simp] theorem regularSplit_coordinates (b : B ⊗[R] S) (g : G) :
    invariantSplit S ρ e he (regularSplit S ρ e he b g) =
      FreeOrbitAlgebra318.coverEquiv G X S (coverSplit S e b) g :=
  (invariantSplit S ρ e he).apply_symm_apply _

/-- The actual intermediate-base extension is a regular split cover. -/
def liftedSplit : (((invariants ρ) ⊗[R] S) ⊗[invariants ρ] B) ≃ₐ[(invariants ρ) ⊗[R] S]
    (G → (invariants ρ) ⊗[R] S) :=
  (TensorTower318.baseEquiv R (invariants ρ) B S).trans (regularSplit S ρ e he)

/-- Exact coordinates of the regular splitting on a generating pure tensor. -/
theorem liftedSplit_tmul_coordinates (a : invariants ρ) (s : S) (b : B)
    (h : G) (x : X) :
    (invariantSplit S ρ e he
      (liftedSplit S ρ e he ((a ⊗ₜ[R] s) ⊗ₜ[invariants ρ] b) h)).1 x =
      e (s ⊗ₜ[R] ((a : B)*b)) (h • (⟦x⟧ : Orbits G X).out) := by
  change (invariantSplit S ρ e he (regularSplit S ρ e he
    (TensorTower318.baseEquiv R (invariants ρ) B S
      ((a ⊗ₜ[R] s) ⊗ₜ[invariants ρ] b)) h)).1 x = _
  rw [regularSplit_coordinates, TensorTower318.baseEquiv_tmul,
    FreeOrbitAlgebra318.coverEquiv_apply, coverSplit_tmul]
  rfl

/-- The regular splitting over the actual invariant base has the exact original
 group action, including its pullback composition convention. -/
theorem liftedSplit_equivariant (g : G)
    (z : ((invariants ρ) ⊗[R] S) ⊗[invariants ρ] B) (h : G) :
    liftedSplit S ρ e he
      (baseAction ((invariants ρ) ⊗[R] S) (fixedAction ρ) g z) h =
        liftedSplit S ρ e he z (g*h) := by
  apply (invariantSplit S ρ e he).injective
  apply Subtype.ext
  funext x
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    induction a using TensorProduct.inductionOn with
    | tmul a s =>
      simp only [baseAction_tmul, liftedSplit_tmul_coordinates]
      have hh := he g (s ⊗ₜ[R] ((a : B)*b))
        (h • (⟦x⟧ : Orbits G X).out)
      simpa only [baseAction_tmul, map_mul, a.property g, mul_smul, fixedAction_apply] using hh
    | add a c ha hc =>
      simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, Subalgebra.coe_add] at *
      rw [ha, hc]
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply, Subalgebra.coe_add] at *
    rw [hz, hw]

attribute [-instance] Algebra.TensorProduct.rightAlgebra

/-- The source splitting over R now produces the canonical torsor algebra
isomorphism over B^G. No regular splitting over B^G is assumed. -/
def invariantTorsorEquiv :
    B ⊗[invariants ρ] B ≃ₐ[invariants ρ] (G → B) := by
  letI : Module.FaithfullyFlat (invariants ρ) ((invariants ρ) ⊗[R] S) := inferInstance
  let q := FaithfullyFlatTorsor318.torsorEquiv_of_faithfullyFlat_split
    ((invariants ρ) ⊗[R] S) (fixedAction ρ) (liftedSplit S ρ e he)
      (liftedSplit_equivariant S ρ e he)
  exact AlgEquiv.ofRingEquiv (f := q.toRingEquiv) (by
    intro a
    ext g
    change (a : B) * fixedAction ρ g 1 = (a : B)
    simp)

@[simp] theorem invariantTorsorEquiv_tmul (b c : B) (g : G) :
    invariantTorsorEquiv S ρ e he (b ⊗ₜ[invariants ρ] c) g = b * ρ g c := rfl

end InvariantRegularSplit318
