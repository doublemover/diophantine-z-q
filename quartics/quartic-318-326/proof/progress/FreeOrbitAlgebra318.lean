module

public import OrbitAlgebra318
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

noncomputable section

open OrbitAlgebra318

namespace FreeOrbitAlgebra318

variable (G X : Type*) [Group G] [MulAction G X] [IsCancelSMul G X]

@[simp] theorem orbit_smul (g : G) (x : X) :
    (⟦g • x⟧ : Orbits G X) = ⟦x⟧ := Quotient.sound ⟨g, rfl⟩

/-- Choose one point in each orbit; the free action parametrizes every point uniquely. -/
def point (a : G × Orbits G X) : X := a.1 • a.2.out

@[simp] theorem point_orbit (g : G) (q : Orbits G X) :
    (⟦point G X (g, q)⟧ : Orbits G X) = q := by
  rw [point, orbit_smul, Quotient.out_eq]

theorem point_bijective : Function.Bijective (point G X) := by
  constructor
  · rintro ⟨g, q⟩ ⟨h, r⟩ he
    have hq : q = r := by
      simpa only [point_orbit] using congrArg (fun x : X => (⟦x⟧ : Orbits G X)) he
    subst r
    have hg : g = h := IsCancelSMul.right_cancel g h q.out he
    subst h
    rfl
  · intro x
    obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (⟦x⟧ : Orbits G X))
    refine ⟨(g⁻¹, ⟦x⟧), ?_⟩
    change g⁻¹ • (⟦x⟧ : Orbits G X).out = x
    rw [← hg]
    simp

def coords : G × Orbits G X ≃ X := Equiv.ofBijective _ (point_bijective G X)

@[simp] theorem coords_apply (g : G) (q : Orbits G X) :
    coords G X (g, q) = g • q.out := rfl

@[simp] theorem coords_symm_orbit (x : X) :
    ((coords G X).symm x).2 = (⟦x⟧ : Orbits G X) := by
  have := point_orbit G X ((coords G X).symm x).1 ((coords G X).symm x).2
  have h := this.symm
  change ((coords G X).symm x).2 =
    (⟦coords G X ((coords G X).symm x)⟧ : Orbits G X) at h
  simpa only [Equiv.apply_symm_apply] using h

variable (R : Type*) [CommRing R]

theorem fixed_out (f : fixedFunctions R G X) (x : X) :
    f.1 (⟦x⟧ : Orbits G X).out = f.1 x := by
  obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (⟦x⟧ : Orbits G X))
  rw [← hg]
  exact f.property g x

/-- Actual algebraic trivialization of a split free-action quotient, over its
actual invariant algebra. This is not merely an equality of ranks. -/
def coverEquiv : (X → R) ≃ₐ[fixedFunctions R G X] (G → fixedFunctions R G X) where
  toFun f g := ⟨fun x => f (g • (⟦x⟧ : Orbits G X).out), by
    intro h x
    dsimp only
    rw [orbit_smul]⟩
  invFun F x := (F ((coords G X).symm x).1).1 x
  left_inv f := by
    funext x
    change f (((coords G X).symm x).1 • (⟦x⟧ : Orbits G X).out) = f x
    rw [← coords_symm_orbit]
    exact congrArg f ((coords G X).apply_symm_apply x)
  right_inv F := by
    funext g
    apply Subtype.ext
    funext x
    change (F ((coords G X).symm (coords G X (g, ⟦x⟧))).1).1
      (g • (⟦x⟧ : Orbits G X).out) = (F g).1 x
    rw [Equiv.symm_apply_apply]
    exact ((F g).property g _).trans (fixed_out G X R (F g) x)
  map_mul' f h := by funext g; apply Subtype.ext; funext x; rfl
  map_add' f h := by funext g; apply Subtype.ext; funext x; rfl
  commutes' f := by
    funext g
    apply Subtype.ext
    funext x
    change f.1 (g • (⟦x⟧ : Orbits G X).out) = f.1 x
    exact (f.property g _).trans (fixed_out G X R f x)

@[simp] theorem coverEquiv_apply (f : X → R) (g : G) (x : X) :
    (coverEquiv G X R f g).1 x = f (g • (⟦x⟧ : Orbits G X).out) := rfl

/-- The actual free cover is a product of copies of its invariant ring. -/
theorem cover_free [Finite G] :
    Module.Free (fixedFunctions R G X) (X → R) := by
  letI : Module.Free (fixedFunctions R G X) (G → fixedFunctions R G X) := inferInstance
  exact Module.Free.of_equiv (coverEquiv G X R).symm.toLinearEquiv

section Torsor
open TensorProduct

variable [Fintype G]

/-- An actual invariant-ring basis of the free cover, indexed by the acting group. -/
def coverBasis : Module.Basis G (fixedFunctions R G X) (X → R) :=
  (Pi.basisFun (fixedFunctions R G X) G).map (coverEquiv G X R).symm.toLinearEquiv

/-- Exact local cover degree, derived from the actual basis. -/
theorem cover_finrank [Nontrivial R] [Nonempty X] :
    Module.finrank (fixedFunctions R G X) (X → R) = Fintype.card G :=
  Module.finrank_eq_card_basis (coverBasis G X R)

/-- Reindex a pair by (g,h) -> (gh,h), an actual bijection even over rings. -/
def matrixTwist (A : Type*) [CommRing A] :
    (G → G → A) ≃ₐ[A] (G → G → A) where
  toFun f g h := f (g*h) h
  invFun f g h := f (g*h⁻¹) h
  left_inv f := by funext g h; simp
  right_inv f := by funext g h; simp
  map_mul' f h := rfl
  map_add' f h := rfl
  commutes' a := rfl

/-- The complete actual split free-action torsor algebra identity. -/
def torsorEquiv :
    (X → R) ⊗[fixedFunctions R G X] (X → R) ≃ₐ[fixedFunctions R G X]
      (G → X → R) := by
  classical
  let A := fixedFunctions R G X
  exact (Algebra.TensorProduct.congr (coverEquiv G X R) (coverEquiv G X R)).trans <|
    (Algebra.TensorProduct.piScalarRight A A (G → A) G).trans <|
      (matrixTwist G A).trans <|
        AlgEquiv.piCongrRight (fun _ : G => (coverEquiv G X R).symm)

/-- The isomorphism is the genuine action map b tensor c -> (g -> b*(g*c)),
not an unidentified isomorphism between free modules of equal rank. -/
theorem torsorEquiv_tmul (b c : X → R) (g : G) :
    torsorEquiv G X R (b ⊗ₜ[fixedFunctions R G X] c) g =
      fun x => b x * c (g • x) := by
  apply (coverEquiv G X R).injective
  change coverEquiv G X R ((coverEquiv G X R).symm
      (fun h => coverEquiv G X R c (g*h) * coverEquiv G X R b h)) = _
  rw [AlgEquiv.apply_symm_apply]
  ext h x
  simp only [Pi.mul_apply, Subalgebra.coe_mul, Pi.mul_apply, coverEquiv_apply, mul_smul]
  exact mul_comm _ _

end Torsor

end FreeOrbitAlgebra318
