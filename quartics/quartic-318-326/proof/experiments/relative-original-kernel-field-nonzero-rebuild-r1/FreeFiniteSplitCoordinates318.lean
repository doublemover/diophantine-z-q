module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Finset.Union
public section
noncomputable section
namespace FreeFiniteSplitCoordinates318
universe u
variable {R A : Type u} [CommRing R] [AddCommGroup A] [Module R A]

/-- Every finite set in a free module lies in a finite free coordinate
summand. Both inclusion and retraction are constructed from the SAME
original basis, so all scalar extensions preserve the coordinate span. -/
lemma exists_split [Module.Free R A] (s : Finset A) :
    ∃ (n : ℕ) (e : (Fin n → R) →ₗ[R] A) (r : A →ₗ[R] (Fin n → R)),
      r.comp e = LinearMap.id ∧ (∀ a ∈ s, ∃ v, e v = a) := by
  classical
  let b := Module.Free.chooseBasis R A
  let t := s.biUnion (fun a => (b.repr a).support)
  let σ := (Fintype.equivFin t).symm
  let n := Fintype.card t
  let e : (Fin n → R) →ₗ[R] A :=
    (Pi.basisFun R (Fin n)).constr R (fun i => b (σ i).val)
  let r : A →ₗ[R] (Fin n → R) := LinearMap.pi (fun i => b.coord (σ i).val)
  have he (i : Fin n) : e ((Pi.basisFun R (Fin n)) i) = b (σ i).val := by
    exact (Pi.basisFun R (Fin n)).constr_basis R _ i
  have hre : r.comp e = LinearMap.id := by
    apply (Pi.basisFun R (Fin n)).ext
    intro i
    apply funext
    intro j
    change b.repr (e ((Pi.basisFun R (Fin n)) i)) (σ j).val =
      ((Pi.basisFun R (Fin n)) i) j
    rw [he]
    have hij : (σ i).val = (σ j).val ↔ i = j :=
      (Subtype.val_injective.comp σ.injective).eq_iff
    simp only [Module.Basis.repr_self_apply, Pi.basisFun_apply, Pi.single_apply, hij]
  have hb (i : Module.Free.ChooseBasisIndex R A) (hi : i ∈ t) :
      b i ∈ LinearMap.range e := by
    let j := (Fintype.equivFin t) ⟨i, hi⟩
    refine ⟨(Pi.basisFun R (Fin n)) j, ?_⟩
    rw [he]
    simp [σ, j]
  refine ⟨n, e, r, hre, ?_⟩
  intro a ha
  change a ∈ LinearMap.range e
  rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply hb
  exact Finset.mem_biUnion.mpr ⟨a, ha, hi⟩
end FreeFiniteSplitCoordinates318
