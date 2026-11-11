module
public import MonomialDegreeFiltration318
public import Mathlib.RingTheory.Adjoin.Basic
public section
noncomputable section
namespace MonomialDegreeExhaustion318
open MonomialDegreeFiltration318
variable {ι K A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing K] [CommRing A] [Algebra K A]

/-- Every element of the actual generated subalgebra has some finite
monomial degree over the ORIGINAL base. This bound can be chosen before
introducing any new normalization scalars. -/
theorem exists_degree (x : ι → A) {a : A}
    (ha : a ∈ Algebra.adjoin K (Set.range x)) :
    ∃ n : ℕ, a ∈ piece (R:=K) x n := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨i,rfl⟩ := ha
    exact ⟨1,by simpa only [pow_one] using generator_power_mem (R:=K) x i 1⟩
  | algebraMap r => exact ⟨0,scalar_mem x r 0⟩
  | add a b ha hb ha' hb' =>
    obtain ⟨m,hm⟩ := ha'
    obtain ⟨n,hn⟩ := hb'
    exact ⟨max m n,(piece x (max m n)).add_mem
      (mono x (le_max_left m n) hm) (mono x (le_max_right m n) hn)⟩
  | mul a b ha hb ha' hb' =>
    obtain ⟨m,hm⟩ := ha'
    obtain ⟨n,hn⟩ := hb'
    exact ⟨m+n,mul_mem x hm hn⟩

/-- The same numerical degree bound persists under extension to the
actual new base scalar ring, provided its scalar tower is the original one. -/
theorem extend_scalars {R : Type*} [CommRing R] [Algebra K R] [Algebra R A]
    [IsScalarTower K R A] (x : ι → A) {n : ℕ} {a : A}
    (ha : a ∈ piece (R:=K) x n) : a ∈ piece (R:=R) x n :=
  Submodule.span_le_restrictScalars K R _ ha

/-- Finitely many actual old-base coefficients admit one common bound,
chosen entirely before any subsequent scalar extension. -/
theorem exists_uniform_degree {J : Type*} [Fintype J] (x : ι → A)
    (c : J → A) (hc : ∀ j, c j ∈ Algebra.adjoin K (Set.range x)) :
    ∃ D : ℕ, ∀ j, c j ∈ piece (R:=K) x D := by
  classical
  choose n hn using fun j => exists_degree x (hc j)
  exact ⟨Finset.univ.sup n,fun j => mono x (Finset.le_sup (Finset.mem_univ j)) (hn j)⟩
end MonomialDegreeExhaustion318
