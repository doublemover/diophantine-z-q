module
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Basic
public section
noncomputable section
namespace CyclicQuotientEvaluation318
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Evaluation of an actual algebra action at its specified cyclic vector.
The coefficient algebra and the entire module are retained. -/
@[expose] def evaluation (ρ : A →ₐ[R] Module.End R M) (v : M) : A →ₗ[R] M where
  toFun a := ρ a v
  map_add' a b := congrArg (fun f : Module.End R M => f v) (map_add ρ a b)
  map_smul' r a := congrArg (fun f : Module.End R M => f v) (map_smul ρ r a)

lemma evaluation_mul (ρ : A →ₐ[R] Module.End R M) (v : M) (a b : A) :
    evaluation ρ v (a*b) = ρ a (evaluation ρ v b) :=
  congrArg (fun f : Module.End R M => f v) (map_mul ρ a b)

/-- The actual annihilator of the marked vector is an ideal, not merely
an R-linear relation space. Stability follows from the original action. -/
@[expose] def ideal (ρ : A →ₐ[R] Module.End R M) (v : M) : Ideal A where
  carrier := {a | evaluation ρ v a = 0}
  zero_mem' := map_zero _
  add_mem' := by intro a b ha hb; rw [map_add,ha,hb,add_zero]
  smul_mem' := by
    intro a b hb
    change evaluation ρ v (a*b) = 0
    rw [evaluation_mul,hb,map_zero]

lemma mem_ideal (ρ : A →ₐ[R] Module.End R M) (v : M) (a : A) :
    a ∈ ideal ρ v ↔ ρ a v = 0 := Iff.rfl

lemma ideal_restrict (ρ : A →ₐ[R] Module.End R M) (v : M) :
    (ideal ρ v).restrictScalars R = LinearMap.ker (evaluation ρ v) := by
  ext a
  rfl
end CyclicQuotientEvaluation318
